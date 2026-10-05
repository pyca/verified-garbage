import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCalls
import VerifiedGarbage.Proof.Pbkdf2.AArch64.IterateCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Pbkdf2.MdKeys

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Pbkdf2`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`, correct

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Pbkdf2.lean`): `pbkdf2` saves our
caller's registers, makes the key (hashing a password longer than a block),
HMAC's states for it and the inner state after the salt.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_addImm wp_subImm wp_movz wp_lsr wp_str eval_zero sub_beq
  toNat_ofNat_lt add_ofNat)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG After SavedRegs SavedRegs.frame save_ok saveR UpdArgs)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne bytesAt_take covers_one)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## Instructions and words -/

theorem wp_subImmW {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 - BitVec.ofNat 32 imm).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .w d n imm :: is)) s Q :=
  VG.Proof.MdStream.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 - BitVec.ofNat 32 imm))
    (by simp [exec, h, State.read]) (k _ (VG.Proof.MdStream.AArch64.Upd.write s .w d _))

/-- `c - 1`, in 32 bits. -/
theorem sub1_32 (x : BitVec 64) (h : 0 < (x.setWidth 32).toNat) :
    (x.setWidth 32 - BitVec.ofNat 32 1).setWidth 64 = BitVec.ofNat 64 ((x.setWidth 32).toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := (x.setWidth 32).isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at h this ⊢
  omega

/-- A shift right leaves zero exactly when the value is below the power of two. -/
theorem shr_beq_zero (x : BitVec 64) (k : Nat) : (x >>> k == 0) = decide (x.toNat < 2 ^ k) := by
  have hk := Nat.two_pow_pos k
  have e : (x >>> k).toNat = x.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : x.toNat < 2 ^ k
  · have : x >>> k = 0 := BitVec.eq_of_toNat_eq (by rw [e, Nat.div_eq_of_lt h]; rfl)
    simp [this, h]
  · have hne : (x >>> k == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have h1 : x.toNat / 2 ^ k = 0 := by rw [← e, h0]; rfl
      have h2 : 2 ^ k ≤ x.toNat := by omega
      have := Nat.div_le_div_right (c := 2 ^ k) h2
      rw [Nat.div_self hk] at this
      omega
    rw [hne]; simp [h]

theorem log2_B (hz : PSizes H) : 2 ^ Nat.log2 H.P.B = H.P.B ∧ Nat.log2 H.P.B < 64 := by
  rcases hz.z.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-! ## What the entry sets up, kept until the salt is absorbed -/

/-- The key's registers: `x19` = `password`, `x20` = `password_len`, `x21` =
`salt`, `x22` = `salt_len`. -/
structure KE (s₀ s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s
  x19 : s.gpr .x19 = pw s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = salt s₀
  x22 : s.gpr .x22 = s₀.gpr .x3

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

/-- The public ones. -/
abbrev epub : List Reg := [.x19, .x20, .x21, .x22, .x23]

theorem kregs_eregs : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs, r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs := by decide

theorem untouched_ne : ∀ r ∈ untouched, r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x9 ∧ r ≠ .x23 ∧
    r ≠ .x4 ∧ r ≠ .x10 := by decide

theorem KE.upd {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_eregs d h'), by rw [u.other _ (ne _ (by simp)), h.x19],
    by rw [u.other _ (ne _ (by simp)), h.x20], by rw [u.other _ (ne _ (by simp)), h.x21],
    by rw [u.other _ (ne _ (by simp)), h.x22]⟩

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem KE.call {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz a.rd a.wr a.sp a.cs a.frame hw, by rw [a.cs _ (by simp [preserved]) (by decide), h.x19],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x20], by rw [a.cs _ (by simp [preserved]) (by decide), h.x21],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x22]⟩

/-! ## The entry -/

theorem entry_ok : WP isa (.block H.entry) s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀) := by
  have hW := hz.W
  have hsnw := hp.snw; have hc0 := hp.c0
  simp only [Hash.entry, Hash.entryPre, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => ?_
  have x4 : s₂.gpr .x4 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have g₂ : ∀ r, r ≠ .x4 → r ≠ .x10 → s₂.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₂.other r h1, u₁.other r h2]
  refine save_ok H.hh (scr := VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (L := (H.W + H.S) * 8) x4 (by show H.W ≤ 1024; exact hz.o_W_le_1024)
    (by rw [u₂.wr, u₁.wr]; exact sc_mem hp) (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L)
    fun s₃ g₃ rd₃ wr₃ sp₃ f₃ sv₃ => ?_
  simp only [Hash.entryPost]
  refine wp_mov fun s₄ u₄ => ?_
  have x23₄ : s₄.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀ := by rw [u₄.gpr, g₃, x4]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, u₂.wr, u₁.wr]
  refine wp_str (a := A s₀ H.outO) ⟨by exact hz.o_outO_mod_8_eq_0, by exact hz.o_outO_lt_4096m8⟩ (by rw [x23₄]) (in_sc hp hz wr₄ (by exact hz.o_outO_8_le_L))
    fun s₅ m₅ => ?_
  refine VG.Proof.Pbkdf2.Md.AArch64.Pbk.wp_subImmW (by decide) fun s₆ u₆ => ?_
  have x23₆ : s₆.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀ := by rw [u₆.other _ (by decide), m₅.gpr, x23₄]
  refine wp_str (a := A s₀ H.cO) ⟨by exact hz.o_cO_mod_8_eq_0, by exact hz.o_cO_lt_4096m8⟩ (by rw [x23₆])
    (by rw [u₆.wr, m₅.wr]; exact in_sc hp hz wr₄ (by exact hz.o_cO_8_le_L)) fun s₇ m₇ => ?_
  refine wp_str (a := A s₀ H.olO) ⟨by exact hz.o_olO_mod_8_eq_0, by exact hz.o_olO_lt_4096m8⟩ (by rw [m₇.gpr, x23₆])
    (by rw [m₇.wr, u₆.wr, m₅.wr]; exact in_sc hp hz wr₄ (by exact hz.o_olO_8_le_L)) fun s₈ m₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ =>
    WP.block_nil ?_
  -- The registers.
  have g₈ : ∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x4 → r ≠ .x10 → s₈.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [m₈.gpr, m₇.gpr, u₆.other r h1, m₅.gpr, u₄.other r h2, g₃, g₂ r h3 h4]
  have g₁₂ : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → s₁₂.gpr r = s₈.gpr r := fun r a b c d => by
    rw [u₁₂.other r d, u₁₁.other r c, u₁₀.other r b, u₉.other r a]
  have v5 : s₄.gpr .x5 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  have v9 : s₆.gpr .x9 = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.gpr, VG.Proof.Pbkdf2.Md.AArch64.Pbk.sub1_32 _ hc0]
  have v6 : s₇.gpr .x6 = s₀.gpr .x6 := by
    rw [m₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  have m₁₂ : s₁₂.mem = ((s₃.mem.writeW (A s₀ H.outO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1))).writeW (A s₀ H.olO) (s₀.gpr .x6) := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, v6, m₇.mem, v9, u₆.mem, m₅.mem, v5, u₄.mem]
  have d_oc : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ :=
    part_disj hz (Or.inl (by exact hz.o_outO_8_le_cO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_cO_8_le_L)
  have d_ol : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.olO, 8⟩ :=
    part_disj hz (Or.inl (by exact hz.o_outO_8_le_olO)) (by exact hz.o_outO_8_le_L) (by exact hz.o_olO_8_le_L)
  have d_cl : Region.Disjoint ⟨A s₀ H.cO, 8⟩ ⟨A s₀ H.olO, 8⟩ :=
    part_disj hz (Or.inl (by exact hz.o_cO_8_le_olO)) (by exact hz.o_cO_8_le_L) (by exact hz.o_olO_8_le_L)
  have fW : Frame [sR s₀ H.outO 24] s₃.mem s₁₂.mem := by
    rw [m₁₂]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by exact hz.o_outO_64d8_le_outO_24)
      (by exact hz.o_outO_24_lt_p64))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_cO) (by exact hz.o_cO_64d8_le_outO_24) (by exact hz.o_outO_24_lt_p64))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by exact hz.o_outO_le_olO) (by exact hz.o_olO_64d8_le_outO_24) (by exact hz.o_outO_24_lt_p64))
  have f₀ : Frame [VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀] s₀.mem s₁₂.mem := by
    have e₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, by simp, part_sub (by exact hz.o_outO_24_le_L)⟩
  have sv : SavedRegs H.hh (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.x19, g₂ _ (by decide) (by decide)], by rw [sv₃.x20, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x21, g₂ _ (by decide) (by decide)], by rw [sv₃.x22, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x24, g₂ _ (by decide) (by decide)], by rw [sv₃.x30, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x23, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, m₈.rd, m₇.rd, u₆.rd, m₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd],
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, m₈.wr, m₇.wr, u₆.wr, m₅.wr, wr₄],
    by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, m₈.sp, m₇.sp, u₆.sp, m₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp],
    by rw [g₁₂ _ (by decide) (by decide) (by decide) (by decide), m₈.gpr, m₇.gpr, x23₆],
    fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := VG.Proof.Pbkdf2.Md.AArch64.Pbk.untouched_ne r hr
      rw [g₁₂ r n1 n2 n3 n4, g₈ r n5 n6 n7 n8],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 56) (Or.inl (by exact hz.o_W8_56_le_outO)) (by exact hz.o_W8_56_le_L) (by exact hz.o_outO_24_le_L),
    by rw [m₁₂, readW_writeW_ne _ _ d_ol, readW_writeW_ne _ _ d_oc, Mem.readW_writeW_self64],
    by rw [m₁₂, readW_writeW_ne _ _ d_cl, Mem.readW_writeW_self64],
    by rw [m₁₂, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]

end

/-! ## Facts about the hash function -/

theorem _root_.VG.Proof.Pbkdf2.Md.AArch64.HashOK.wb_le (hH : HashOK H) : hH.stream.Wb ≤ 8 * H.W := by
  have := hH.stream.hWb; have e : H.stream.W = (H.P.so + 48) / 8 := rfl; have := hH.sizes.fits; omega

theorem PSizes.o_hsWb_le_L (hz : PSizes H) (hH : HashOK H) : hH.stream.Wb ≤ (H.W + H.S) * 8 := by
  have := hH.wb_le; have := hz.W; omega

theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.sizes.DN; omega

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hl := VG.Proof.Pbkdf2.Md.AArch64.Pbk.hash_len hH k; have hB := hH.hB; have := hH.sizes.pad
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega))]

theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  have hB := hH.hB; have := hH.sizes.pad
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.hash_len]; omega
  · omega

theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega) hi) hr

/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (VG.WriteBytes.writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-! ## Hashing a password longer than a block -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp in
theorem hk1_ok {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) :
    WP isa (.block H.hkInit) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO := by
  simp only [Hash.hkInit]
  exact wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), by rw [u₁.gpr, h.kr.x23]⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (hx0 : s.gpr .x0 = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  exact VG.Proof.Pbkdf2.Md.AArch64.Calls.init_call hH.stream (st := A s₀ H.stWO) hx0
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by exact hz.o_stWO_hsS_le_L))
    fun s₂ a₂ r₂ => ⟨h.call hp hz a₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block H.hkUpd) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (pwl s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  simp only [Hash.hkUpd]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x19]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cd := covers_one (List.mem_append_left _ (by rw [k₅.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₅.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp k₅.kr (by exact hz.o_hsWb_le_L hH)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
      d_st := hp.pw_s.sub_right (part_sub (by exact hz.o_stWO_hsS_le_L))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by exact hz.o_hsWb_le_L hH))
      sp16 := by rw [k₅.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₅.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := by rw [k₅.kr.sp]; exact hp.stk_pw
      stk_sc := stk_sc hp k₅.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s)
    (ua : UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (pwl s₀))
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream ua fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr hx1
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block H.hkFin) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) ∧
      t.gpr .x1 = s₀.gpr .x1 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [Hash.hkFin]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addImm (by exact hz.o_hkO_lt_4096) fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => WP.block_nil ?_
  have k₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨k₄, ?_, by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x20],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      x3 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₄.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_part hp k₄.kr (by exact hz.o_hkO_hsF_le_L)
        · exact cov_low hp k₄.kr (by exact hz.o_hsWb_le_L hH)
      st_o := part_disj hz (Or.inl (by exact hz.o_stWO_hsS_le_hkO)) (by exact hz.o_stWO_hsS_le_L) (by exact hz.o_hkO_hsF_le_L)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
      o_sc := (low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_hsF_le_L)).sub_right (Region.sub_prefix hWb)
      sp16 := by rw [k₄.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₄.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_o := stk_sc hp k₄.kr (part_sub (by exact hz.o_hkO_hsF_le_L))
      stk_sc := stk_sc hp k₄.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s)
    (fa : VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀))
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hWb := hH.wb_le; have hD := hz.z.DN
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stWO, by exact hz.o_stWO_hsS_le_L⟩
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_hkO, by exact hz.o_hkO_hsF_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ (show H.D ≤ H.stream.F by exact hz.o_D_le_hsF)]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .x1).isLt)
      (by rw [hx1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) :
    WP isa (.block H.hkKey) s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧ t.mem = s.mem := by
  have hD := hz.z.DN; have hN := hz.N
  simp only [Hash.hkKey]
  refine wp_addImm (by exact hz.o_hkO_lt_4096) fun s₁ u₁ => wp_movz fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.kr.x23],
    by rw [u₂.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.D < 2 ^ 16 by exact hz.o_D_lt_p16), Nat.mod_eq_of_lt (show H.D < 2 ^ 64 by exact hz.o_D_lt_p64)],
    by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-! ## The key -/

/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hz in
theorem short_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (hs : pwl s₀ < H.P.B + 1) :
    WP isa (.block Hash.short) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ ∧
      (t.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) := by
  have e₁ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  have e₂ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  rw [e₁, e₂]
  simp only [Hash.short]
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil ?_
  refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.x19],
    by rw [u₂.gpr, u₁.other _ (by decide), h.x20], ⟨.inl ⟨rfl, rfl⟩, by omega, ?_⟩⟩
  rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

theorem long_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (hs : ¬ pwl s₀ < H.P.B + 1) :
    WP isa H.hashKey s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ ∧
      (t.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) := by
  have hD := hz.z.DN; have := hz.z.pad
  have e₁ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hs)
  have e₂ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hs)
  rw [e₁, e₂]
  refine WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hashKey_ok hp hz hH h) fun t ⟨k, x2, x3, hb⟩ =>
    ⟨k, x2, x3, ⟨.inr ⟨rfl, rfl⟩, by exact hz.o_D_le_B, ?_⟩⟩
  rw [hb, VG.Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_hash hH (by rw [bytesAt_length]; omega)]

omit hp in
/-- The value of `x9` the key's first branch tests. -/
theorem key_shr {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) {s₁ : State}
    (u : Upd s s₁ .x9 (s.gpr .x20 >>> Nat.log2 H.P.B)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (pwl s₀ < H.P.B)) := by
  change eval (.zero .x .x9) s₁ = _
  rw [eval_zero, u.gpr, h.x20, VG.Proof.Pbkdf2.Md.AArch64.Pbk.shr_beq_zero, (VG.Proof.Pbkdf2.Md.AArch64.Pbk.log2_B hz).1]

omit hp hz in
/-- The value of `x9` the key's second branch tests. -/
theorem key_sub {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) {s₂ : State}
    (u : Upd s s₂ .x9 (s.gpr .x20 - BitVec.ofNat 64 H.P.B)) (hB : H.P.B < 2 ^ 64) :
    isa.eval (.zero .x .x9) s₂ = some (decide (pwl s₀ = H.P.B)) := by
  change eval (.zero .x .x9) s₂ = _
  have ex : s₀.gpr .x1 = BitVec.ofNat 64 (pwl s₀) := by simp
  rw [eval_zero, u.gpr, h.x20, ex, sub_beq (s₀.gpr .x1).isLt hB]

theorem key_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) :
    WP isa H.key s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ ∧ (t.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ ∧
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) := by
  have hB := hz.B_le
  unfold Hash.key Hash.keyShr Hash.keySub
  refine WP.seq (wp_lsr (VG.Proof.Pbkdf2.Md.AArch64.Pbk.log2_B hz).2 fun s₁ u₁ => WP.block_nil ?_)
  have k₁ := h.upd u₁ (by decide)
  refine WP.ite _ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_shr hz h u₁) (fun hT => VG.Proof.Pbkdf2.Md.AArch64.Pbk.short_ok hp hH k₁ (by have := of_decide_eq_true hT; omega))
    fun hF => ?_
  refine WP.seq (wp_subImm (by exact hz.o_B_lt_4096) fun s₂ u₂ => WP.block_nil ?_)
  have k₂ := k₁.upd u₂ (by decide)
  refine WP.ite _ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_sub k₁ u₂ (by exact hz.o_B_lt_p64)) (fun hT => VG.Proof.Pbkdf2.Md.AArch64.Pbk.short_ok hp hH k₂ (by
    have := of_decide_eq_true hT; omega)) fun hF' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.long_ok hp hz hH k₂ (by
      have := of_decide_eq_false hF; have := of_decide_eq_false hF'; omega)

/-! ## HMAC's states -/

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ m' := by
  exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by exact hz.o_st0O_S_le_st0O_3mS))) h.i,
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_st0O_3mS))) h.o,
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_st0O_3mS))) h.s⟩

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ m kp kl) {s : State}
    (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below s.sp 16).Disjoint ⟨kp, kl⟩ := by
  have hD := hz.z.DN; have hN := hz.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by exact hz.o_st0O_S_le_L)), hp.pw_s.sub_right (part_sub (by exact hz.o_st1O_S_le_L)),
      hp.pw_s.sub_right low_sub, by rw [h.sp]; exact hp.stk_pw⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by exact hz.o_st0O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st0O_S_le_L),
      part_disj hz (Or.inr (by exact hz.o_st1O_S_le_hkO)) (by exact hz.o_hkO_D_le_L) (by exact hz.o_st1O_S_le_L), low_disj hz (by exact hz.o_W8_le_hkO) (by exact hz.o_hkO_D_le_L),
      stk_sc hp h (part_sub (by exact hz.o_hkO_D_le_L))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by exact hz.o_hkO_D_le_L)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (hx2 : s.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀)
    (hx3 : (s.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) (hk : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀)) :
    WP isa (.block H.initArgs) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) ∧
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) := by
  have hL := L_lt hz
  have hsnw := hp.snw
  simp only [Hash.initArgs]
  refine wp_addImm (by exact hz.o_st0O_lt_4096) fun s₁ u₁ => wp_addImm (by exact hz.o_st1O_lt_4096) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { x0 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x1 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.kr.x23]
      x2 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx2]
      x3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx3]
      x4 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₃.kr (by exact hz.o_st0O_S_le_L)
        · exact cov_part hp k₃.kr (by exact hz.o_st1O_S_le_L)
        · exact cov_low hp k₃.kr (by exact hz.o_W8_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_st0O_S_le_st1O)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      k_i := k_i
      k_o := k_o
      k_s := k_s
      sp16 := by rw [k₃.kr.sp]; exact hp.sp16
      stk_i := stk_sc hp k₃.kr (part_sub (by exact hz.o_st0O_S_le_L))
      stk_o := stk_sc hp k₃.kr (part_sub (by exact hz.o_st1O_S_le_L))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr low_sub
      scnw := by show (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀))
    (hk : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) opad) := by
  refine hinit_call hH hI hId ia fun s₄ a₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz a₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_st0O_S_le_L⟩
      · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_st1O, by exact hz.o_st1O_S_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-- The inner state copied, and `update`'s arguments: the salt. -/
theorem su3_ok (hH : HashOK H) {s₄ : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s₄)
    (ri₄ : hH.SH.Repr s₄.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad))
    (ro₄ : hH.SH.Repr s₄.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) opad)) :
    WP isa (.block H.saltArgs) s₄ fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (sl s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad) := by
  have hWb := hH.wb_le
  have hB := hz.B_le; have hN4 := hz.z.N4
  have hB4 : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> exact hz.o_B_mod_4_eq_0
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have eS : 4 * (H.S / 4) = H.S := by exact hz.o_4mSd4_eq_S
  simp only [Hash.saltArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.st0O H.stSO (H.S / 4)
    ⟨by exact hz.o_st0O_mod_4_eq_0, by exact hz.o_st0O_4mSd4_le_4096m4⟩ ⟨by exact hz.o_stSO_mod_4_eq_0, by exact hz.o_stSO_4mSd4_le_4096m4⟩ _ s₄ _
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_rw hp hz h.kr (by omega_using [hj, hz.o_st0O_S_le_L]))
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (by rw [h.kr.x23, eS]; exact (part_disj hz (Or.inl (by exact hz.o_st0O_S_le_stSO)) (by exact hz.o_st0O_S_le_L) (by exact hz.o_stSO_S_le_L)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  rw [h.kr.x23, eS] at m₅
  have f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [m₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have g : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, s₅.gpr r = s₄.gpr r := fun r hr => g₅ r (by rintro rfl; revert hr; decide)
  have k₅ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s₅ := ⟨h.kr.write hz rd₅ wr₅ sp₅ (fun r hr => g r (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_eregs r hr))
      (o := H.stSO) (n := H.S) (by exact hz.o_st0O_le_stSO) (by exact hz.o_stSO_S_le_L) f₅,
    by rw [g _ (by simp), h.x19], by rw [g _ (by simp), h.x20], by rw [g _ (by simp), h.x21],
    by rw [g _ (by simp), h.x22]⟩
  have dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r :=
    fun o ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_S_le_L)
  have ri₅ := VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH f₅ (dS _ (by exact hz.o_st0O_S_le_stSO)) ri₄
  have ro₅ := VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH f₅ (dS _ (by exact hz.o_st1O_S_le_stSO)) ro₄
  have rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad) := by rw [m₅]; exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_copy hH ri₄
  refine wp_addImm (by exact hz.o_stSO_lt_4096) fun s₆ u₆ => wp_movz fun s₇ u₇ => wp_mov fun s₈ u₈ =>
    wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => WP.block_nil ?_
  have k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  have m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, ?_, m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  · exact
      { x0 := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
            u₇.other _ (by decide), u₆.gpr, k₅.kr.x23]
        x2 := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.x21]
        x3 := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.x22]
        x4 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.kr.x23]
        cd := covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
        cw := Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp k₁₀.kr (by exact hz.o_stSO_hsS_le_L)
          · exact cov_low hp k₁₀.kr (by exact hz.o_hsWb_le_L hH)
        st_sc := (low_disj hz (by exact hz.o_W8_le_stSO) (by exact hz.o_stSO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
        d_st := hp.sa_s.sub_right (part_sub (by exact hz.o_stSO_hsS_le_L))
        d_sc := hp.sa_s.sub_right (Region.sub_prefix (by exact hz.o_hsWb_le_L hH))
        sp16 := by rw [k₁₀.kr.sp]; exact hp.sp16
        stk_st := stk_sc hp k₁₀.kr (part_sub (by exact hz.o_stSO_hsS_le_L))
        stk_d := by rw [k₁₀.kr.sp]; exact hp.stk_sa
        stk_sc := stk_sc hp k₁₀.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.P.B < 2 ^ 16 by exact hz.o_B_lt_p16), Nat.mod_eq_of_lt (show H.P.B < 2 ^ 64 by exact hz.o_B_lt_p64)]

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s₁₀)
    (ua : UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (sl s₀))
    (hx1 : s₁₀.gpr .x1 = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ t.mem := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream ua fun s₁₁ a₁₁ r₁₁ => ?_
  have k₁₁ := k₁₀.call hp hz a₁₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by exact hz.o_st0O_le_stSO, by exact hz.o_stSO_hsS_le_L⟩
    · exact .inl ⟨_, rfl, hWb⟩
  have dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region),
      ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, hH.stream.Wb⟩] ++ [below s₁₀.sp 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega_using [ho, hz.o_stSO_S_le_L]) (by exact hz.o_stSO_hsS_le_L)
      · exact (low_disj hz (by omega_using [ho₀, hz.o_W8_le_st0O]) (by omega_using [ho, hz.o_stSO_S_le_L])).sub_right (Region.sub_prefix hWb)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (stk_sc hp k₁₀.kr (part_sub (by omega_using [ho, hz.o_stSO_S_le_L]))).symm
  refine ⟨k₁₁, ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st0O) (by exact hz.o_st0O_S_le_stSO)) ri,
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH a₁₁.frame (dW _ (by exact hz.o_st0O_le_st1O) (by exact hz.o_st1O_S_le_stSO)) ro, ?_⟩⟩
  have := r₁₁ _ rs (by rw [hx1, xorPad_length, VG.Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.aarch64Depth ≤ 1) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s)
    (hx2 : s.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (hx3 : (s.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) (hk : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀)) :
    WP isa H.setup s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.su1_ok hp hz hH h hx2 hx3 hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.su2_ok hp hz hH hI hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, x₃, i₃, o₃, r₃⟩ => ?_)
  exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.su4_ok hp hz hH k₃ a₃ x₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkLoop`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s loop

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkLoop.lean`): after `k` blocks of the
output (`Inv`), `out` holds the first `min (k D) out_len` bytes of `T₁ ‖ … ‖
T_k`; a step computes `T_{k+1}` (`U₁` by `update` with `INT (k + 1)` and
HMAC's `finalize`, then `iterate`) and copies as much of it as the output
still needs.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_addImm wp_subImm wp_movz wp_lsr wp_ldr wp_str32 wp_ldrb
  wp_strb wp_add wp_sub wp_rev32 eval_zero eval_nonzero sub_ofNat add_ofNat ofNat_succ ofNat_beq_zero writeW32
  setWidth32)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After UpdArgs restore_ok savedRegs CopyInv clob nm count_loop
  movz_ofNat ofNat_ne_zero)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_snoc' writeBytes_snoc not_mem_of_disjoint
  bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The specification's pieces -/

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hH : HashOK H) (s₀ : State) : List Byte → List Byte := hmacBlockKey hH.SH.H (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀)

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem (salt s₀) (sl s₀)

/-- `T_i`. -/
abbrev Tb (hH : HashOK H) (s₀ : State) (i : Nat) : List Byte := Spec.Pbkdf2.F (VG.Proof.Pbkdf2.Md.AArch64.Pbk.prf hH s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀) (cc s₀) i

/-- `T₁ ‖ … ‖ T_k`. -/
def G (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte := (List.range k).flatMap fun j => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Tb hH s₀ (j + 1)

theorem G_succ (hH : HashOK H) (s₀ : State) (k : Nat) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ (k + 1) = VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ k ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Tb hH s₀ (k + 1) := by
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Pbk.G, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The number of blocks of the output. -/
abbrev nb (H : Hash) (s₀ : State) : Nat := (ol s₀ + H.D - 1) / H.D

/-- The bytes of the output after `k` blocks. -/
abbrev done (H : Hash) (s₀ : State) (k : Nat) : Nat := min (k * H.D) (ol s₀)

theorem lt_nb {s₀ : State} (hD : 0 < H.D) {k : Nat} : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ ↔ k * H.D < ol s₀ := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega

theorem ol_le {s₀ : State} (hD : 0 < H.D) : ol s₀ ≤ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ * H.D := by
  have h1 : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ * H.D + (ol s₀ + H.D - 1) % H.D = ol s₀ + H.D - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have h2 := Nat.mod_lt (ol s₀ + H.D - 1) hD
  omega

theorem nb_lt {s₀ : State} (hD : 0 < H.D) (h : ol s₀ ≤ (2 ^ 32 - 1) * H.D) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]; omega

theorem nb_zero {s₀ : State} (hD : 0 < H.D) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ = 0 ↔ ol s₀ = 0 := by
  have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb (s₀ := s₀) hD (k := 0); simp only [Nat.zero_mul] at this; omega

/-! ## Facts about words, lengths and registers -/

theorem bytes32_int (i : Nat) : VG.Proof.MdStream.bytes32 true (BitVec.ofNat 32 i) = Spec.Pbkdf2.int i := by
  simp only [VG.Proof.MdStream.bytes32, ite_true, Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;> omega

/-- Two disjoint regions that do not wrap around fit in the address space
together. -/
theorem len_add_le {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) (h₁ : r₁.base.toNat + r₁.len ≤ 2 ^ 64)
    (h₂ : r₂.base.toNat + r₂.len ≤ 2 ^ 64) : r₁.len + r₂.len ≤ 2 ^ 64 := by
  by_contra hc
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with hb | hb
  · refine hd r₂.base ?_ ?_ <;> simp only [Region.Contains]
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine hd r₁.base ?_ ?_ <;> simp only [Region.Contains]
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega

theorem eregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem eregs_clob : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, r ∉ clob := by decide

theorem kregs_clob : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs, r ∉ clob := by decide

/-- A do-while loop on `x21 ≠ 0` whose body runs `n > 0` times. -/
theorem nb_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧
      isa.eval (.nonzero .x .x21) s' = some (decide (k + 1 ≠ n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x .x21)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The loop's invariant -/

/-- After `k` blocks of the output: `x19` is the next block's number, `x20`
`salt_len`, `x21` the bytes left and `x22` where they go. -/
structure Inv (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s
  st : VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ s.mem
  x19 : s.gpr .x19 = BitVec.ofNat 64 (k + 1)
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = BitVec.ofNat 64 (ol s₀ - VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ k)
  x22 : s.gpr .x22 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ + BitVec.ofNat 64 (VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ k)
  glen : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ k).length = k * H.D
  outB : bytesAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ k) = (VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ k).take (VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ k)

/-- In step `k`, before `T_{k+1}` is copied out. -/
structure Mid (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s
  st : VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ s.mem
  x19 : s.gpr .x19 = BitVec.ofNat 64 (k + 1)
  x20 : s.gpr .x20 = s₀.gpr .x3
  x21 : s.gpr .x21 = BitVec.ofNat 64 (ol s₀ - k * H.D)
  x22 : s.gpr .x22 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D)
  outB : bytesAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀) (k * H.D) = VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ k

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem loopRegs_ok (hH : HashOK H) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (hS : VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ s.mem) :
    WP isa (.block H.loopRegs) s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀ = 0)) := by
  simp only [Hash.loopRegs]
  refine wp_mov fun s₁ u₁ => ?_
  have k₁ := h.kr.upd u₁ (by decide)
  refine wp_ldr (a := A s₀ H.outO) ⟨by exact hz.o_outO_mod_8_eq_0, by exact hz.o_outO_lt_4096m8⟩ (by rw [k₁.x23]) (in_rw hp hz k₁ (by exact hz.o_outO_8_le_L))
    fun s₂ u₂ => ?_
  have k₂ := k₁.upd u₂ (by decide)
  refine wp_ldr (a := A s₀ H.olO) ⟨by exact hz.o_olO_mod_8_eq_0, by exact hz.o_olO_lt_4096m8⟩ (by rw [k₂.x23]) (in_rw hp hz k₂ (by exact hz.o_olO_8_le_L))
    fun s₃ u₃ => ?_
  have k₃ := k₂.upd u₃ (by decide)
  refine wp_movz fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have x21 : s₄.gpr .x21 = BitVec.ofNat 64 (ol s₀) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.kr.olW, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨k₃.upd u₄ (by decide), m₄ ▸ hS, by rw [u₄.gpr]; rfl, ?_, ?_, ?_, by simp [VG.Proof.Pbkdf2.Md.AArch64.Pbk.G], by simp [bytesAt]⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x22]
  · rw [x21]; simp
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, h.kr.outW]; simp
  · change eval (.zero .x .x21) s₄ = _
    rw [eval_zero, x21, ofNat_beq_zero (s₀.gpr .x6).isLt]

/-- What writes leave: they are in the working space of the functions we
call, in `scratch` from the working state on, or the 16 bytes below the
stack pointer. -/
theorem Mid.keep (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, (∃ j, r = ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      (∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) ∨ r = below s.sp 16) :
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s' := by
  have ho : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀, k * H.D⟩ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀) := Region.sub_prefix hk
  have key : ∀ {X : Region}, (∀ o j, H.stWO ≤ o → o + j ≤ (H.W + H.S) * 8 → X.Disjoint (sR s₀ o j)) →
      X.Disjoint (lowR (H := H) s₀) → X.Disjoint (below s.sp 16) → ∀ r ∈ rs, X.Disjoint r := by
    intro X h1 h2 h3 r hr
    rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, ho1, ho2⟩ | rfl
    · exact h2.sub_right (Region.sub_prefix hj)
    · exact h1 o j ho1 ho2
    · exact h3
  have hstk : ∀ {X : Region}, Region.Sub X (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀) → X.Disjoint (below s.sp 16) :=
    fun hX => (stk_sc hp h.kr hX).symm
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_eregs r hr)) hf
      (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_sv_80_le_stWO])) (by exact hz.o_sv_80_le_L) h2) (low_disj hz (by exact hz.o_W8_le_sv) (by exact hz.o_sv_80_le_L))
        (hstk (part_sub (by exact hz.o_sv_80_le_L)))) (fun r hr => ?_),
    h.st.keep hz hH hf (key (fun o j h1 h2 => part_disj hz (Or.inl (by omega_using [h1, hz.o_st0O_3mS_le_stWO])) (by exact hz.o_st0O_3mS_le_L) h2)
      (low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_3mS_le_L)) (hstk (part_sub (by exact hz.o_st0O_3mS_le_L)))),
    by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20],
    by rw [hg _ (by simp), h.x21], by rw [hg _ (by simp), h.x22], ?_⟩
  · rcases hw r hr with ⟨j, rfl, hj⟩ | ⟨o, j, rfl, _, h2⟩ | rfl
    · exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, by simp, Region.sub_prefix (by show j ≤ (H.W + H.S) * 8; omega)⟩
    · exact ⟨_, by simp, part_sub h2⟩
    · rw [h.kr.sp]
      exact ⟨_, by simp, fun _ h => h⟩
  · rw [← h.outB]
    exact bytes_keep hf (key (fun o j _ h2 => (hp.o_s.sub_left ho).sub_right (part_sub h2))
      ((hp.o_s.sub_left ho).sub_right low_sub) (by rw [h.kr.sp]; exact (hp.stk_o.sub_right ho).symm))
      (by have := hp.onw; omega)

/-- What a call leaves. -/
theorem Mid.call (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s)
    {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ j, r = ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, j⟩ ∧ j ≤ 8 * H.W) ∨
      ∃ o j, r = sR s₀ o j ∧ H.stWO ≤ o ∧ o + j ≤ (H.W + H.S) * 8) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s' :=
  h.keep hp hz hH hk a.rd a.wr a.sp (fun r hr => a.cs r (VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs_pres r hr).2) a.frame
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rcases hw r hr with h1 | h2
        · exact .inl h1
        · exact .inr (.inl h2)
      · simp only [List.mem_singleton] at hr; exact .inr (.inr hr)

/-- A write into a part of `scratch` from the working state on. -/
theorem Mid.write (hH : HashOK H) {k : Nat} (hk : k * H.D ≤ ol s₀) {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, s'.gpr r = s.gpr r)
    {o n : Nat} (ho : H.stWO ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [sR s₀ o n] s.mem s'.mem) :
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s' :=
  h.keep hp hz hH hk hrd hwr hsp hg hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl ⟨o, n, rfl, ho, hon⟩)

omit hp hz in
theorem Mid.upd {hH : HashOK H} {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s) {d : Reg} {v : BitVec 64}
    (u : Upd s s' d v) (hd : d ∉ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s' := by
  have ne : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_eregs d h'), u.mem ▸ h.st,
    by rw [u.other _ (ne _ (by simp)), h.x19], by rw [u.other _ (ne _ (by simp)), h.x20],
    by rw [u.other _ (ne _ (by simp)), h.x21], by rw [u.other _ (ne _ (by simp)), h.x22],
    by rw [u.mem, h.outB]⟩

end

/-! ## Copying `T` out -/

theorem outLoop_ok {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 63) (htO : H.tO < 4096) {s : State}
    (hc : s.gpr .x11 = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 H.tO + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .x23 + BitVec.ofNat 64 H.tO, n⟩ ⟨s.gpr .x22, n⟩) :
    WP isa H.outLoop s fun t => CopyInv s (s.gpr .x23 + BitVec.ofNat 64 H.tO) (s.gpr .x22) n t := by
  have e23 : ∀ {A B : Addr} {k : Nat} {t : State}, CopyInv s A B k t → t.gpr .x23 = s.gpr .x23 :=
    fun h => h.other .x23 (by decide)
  have e22 : ∀ {A B : Addr} {k : Nat} {t : State}, CopyInv s A B k t → t.gpr .x22 = s.gpr .x22 :=
    fun h => h.other .x22 (by decide)
  generalize eA : s.gpr .x23 + BitVec.ofNat 64 H.tO = A at hin hsep ⊢
  generalize eB : s.gpr .x22 = B at hout hsep ⊢
  unfold Hash.outLoop
  refine WP.seq (wp_movz fun s₀ u₀ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ ∧ s₀.gpr .x11 = BitVec.ofNat 64 (n - 0) :=
    ⟨⟨u₀.rd, u₀.wr, u₀.sp, fun r hr => u₀.other r (nm hr .x24), by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩,
      by rw [u₀.other _ (by decide), hc, Nat.sub_zero]⟩
  refine WP.mono (count_loop hn (by omega)
    (fun k t => CopyInv s A B k t ∧ t.gpr .x11 = BitVec.ofNat 64 (n - k)) (fun k hk t h => ?_) i0)
    fun t h => h.1
  obtain ⟨h, h11⟩ := h
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) htO
    (by rw [u₁.gpr, e23 h, h.x24, ← eA]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) (by decide)
    (by rw [u₃.gpr, u₂.other .x22 (by decide), u₁.other .x22 (by decide), e22 h, u₂.other .x24 (by decide),
      u₁.other .x24 (by decide), h.x24, eB]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_addImm (by decide) fun t₅ u₅ => wp_subImm (by decide) fun t₆ u₆ => WP.block_nil ?_
  have h24 : t₅.gpr .x24 = BitVec.ofNat 64 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x24]
    exact (ofNat_succ k).symm
  have x11 : t₆.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h11, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (nm hr .x11), u₅.other r (nm hr .x24), m₄.gpr, u₃.other r (nm hr .x13),
        u₂.other r (nm hr .x9), u₁.other r (nm hr .x12), h.other r hr],
    by rw [u₆.other _ (by decide), h24], ?_⟩, x11⟩, x11⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  have v : (t₃.gpr .x9).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
    simp only [VG.WriteBytes.writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
    ext i hi; simp
  have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega)
  rw [hl] at e'
  rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']

/-! ## A step: `U₁` -/

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : PSizes H)
include hp hz

/-- `U₁ = PRF (S ‖ INT (k + 1))`. -/
abbrev U1 (hH : HashOK H) (s₀ : State) (k : Nat) : List Byte :=
  hmacBlockKey hH.SH.H (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

omit hp hz in
/-- Before `update` with `INT (k + 1)`. -/
structure AtUpd (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s
  args : UpdArgs hH.stream s (A s₀ H.stWO) (A s₀ H.intO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) 4
  x1 : s.gpr .x1 = BitVec.ofNat 64 (H.P.B + sl s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀)
  int : bytesAt s.mem (A s₀ H.intO) 4 = Spec.Pbkdf2.int (k + 1)

omit hp hz in
/-- Before HMAC's `finalize`. -/
structure AtFin (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s
  args : FinArgs (H := H) s (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .x3 + BitVec.ofNat 64 (H.P.B + 4))
    (A s₀ H.uO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀)
  repr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))

omit hp hz in
/-- Before `iterate`. -/
structure AtIter (hH : HashOK H) (s₀ : State) (k : Nat) (s : State) : Prop where
  mid : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s
  args : IterArgs (H := H) s (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀)
  u : bytesAt s.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.U1 hH s₀ k
  t : bytesAt s.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.U1 hH s₀ k

/-- A copy of the salted inner state, `INT (k + 1)`, and `update`'s arguments. -/
theorem pieceA_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s) :
    WP isa (.block H.intArgs) s (VG.Proof.Pbkdf2.Md.AArch64.Pbk.AtUpd hH s₀ k) := by
  have hWb := hH.wb_le
  have hB := hz.B_le; have hN4 := hz.z.N4; have hD := hz.z.D0; have hD4 := hz.z.D4; have hDN := hz.z.DN
  have hN := hz.N
  have hB4 : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> exact hz.o_B_mod_4_eq_0
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have eS : 4 * (H.S / 4) = H.S := by exact hz.o_4mSd4_eq_S
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hD).1 hk
  have hk' := Nat.le_of_lt hkD
  have hk32 : k + 1 < 2 ^ 32 := by have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_lt hD hp.olD; omega
  -- The salted inner state, copied.
  simp only [Hash.intArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.stSO H.stWO (H.S / 4)
    ⟨by exact hz.o_stSO_mod_4_eq_0, by exact hz.o_stSO_4mSd4_le_4096m4⟩ ⟨by exact hz.o_stWO_mod_4_eq_0, by exact hz.o_stWO_4mSd4_le_4096m4⟩ _ s _
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_rw hp hz h.kr (by omega_using [hj, hz.o_stSO_S_le_L]))
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega_using [hj, hz.o_stWO_S_le_L]))
    (by rw [h.kr.x23, eS]; exact (part_disj hz (Or.inl (by exact hz.o_stSO_S_le_stWO)) (by exact hz.o_stSO_S_le_L) (by exact hz.o_stWO_S_le_L)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [h.kr.x23, eS] at m₁
  have f₁ : Frame [sR s₀ H.stWO H.S] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have md₁ := h.write hp hz hH hk' rd₁ wr₁ sp₁ (fun r hr => g₁ r (by rintro rfl; revert hr; decide))
    (o := H.stWO) (n := H.S) (Nat.le_refl _) (by exact hz.o_stWO_S_le_L) f₁
  have rs₁ : hH.SH.Repr s₁.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀) := by
    rw [m₁]; exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_copy hH h.st.s
  -- `INT (k + 1)`.
  refine wp_rev32 fun s₂ u₂ => ?_
  have md₂ := md₁.upd u₂ (by decide)
  refine wp_str32 (a := A s₀ H.intO) ⟨by exact hz.o_intO_mod_4_eq_0, by exact hz.o_intO_lt_4096m4⟩ (by rw [md₂.kr.x23])
    (in_sc hp hz md₂.kr.wr (by exact hz.o_intO_4_le_L)) fun s₃ g₃ => ?_
  have f₃ : Frame [sR s₀ H.intO 4] s₂.mem s₃.mem := by
    rw [g₃.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have md₃ := md₂.write hp hz hH hk' g₃.rd g₃.wr g₃.sp (fun r _ => by rw [g₃.gpr]) (o := H.intO) (n := 4)
    (by exact hz.o_stWO_le_intO) (by exact hz.o_intO_4_le_L) f₃
  have e₃ : s₃.mem = VG.WriteBytes.writeBytes s₂.mem (A s₀ H.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [g₃.mem, u₂.gpr, setWidth32, md₁.x19,
      show (BitVec.ofNat 64 (k + 1)).setWidth 32 = BitVec.ofNat 32 (k + 1) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega),
      show rev32 (BitVec.ofNat 32 (k + 1)) = if true then rev32 (BitVec.ofNat 32 (k + 1)) else _ from rfl,
      writeW32, VG.Proof.Pbkdf2.Md.AArch64.Pbk.bytes32_int]
  -- `update`'s arguments.
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₄ u₄ => wp_addImm (by exact hz.o_B_lt_4096) fun s₅ u₅ => wp_addImm (by exact hz.o_intO_lt_4096) fun s₆ u₆ =>
    wp_movz fun s₇ u₇ => wp_mov fun s₈ u₈ => WP.block_nil ?_
  have md₈ := ((((md₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)).upd u₈
    (by decide)
  have e₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have ua : UpdArgs hH.stream s₈ (A s₀ H.stWO) (A s₀ H.intO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) 4 :=
    { x0 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, md₃.kr.x23]
      x2 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
          u₄.other _ (by decide), md₃.kr.x23]
      x3 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
      x4 := by rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), md₃.kr.x23]
      cd := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp md₈.kr (o := H.intO) (n := 4) (by exact hz.o_intO_4_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp md₈.kr (by exact hz.o_stWO_hsS_le_L)
        · exact cov_low hp md₈.kr (by exact hz.o_hsWb_le_L hH)
      st_sc := (low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_hsS_le_L)).sub_right (Region.sub_prefix hWb)
      d_st := part_disj hz (Or.inr (by exact hz.o_stWO_hsS_le_intO)) (by exact hz.o_intO_4_le_L) (by exact hz.o_stWO_hsS_le_L)
      d_sc := (low_disj hz (by exact hz.o_W8_le_intO) (by exact hz.o_intO_4_le_L)).sub_right (Region.sub_prefix hWb)
      sp16 := by rw [md₈.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp md₈.kr (part_sub (by exact hz.o_stWO_hsS_le_L))
      stk_d := stk_sc hp md₈.kr (part_sub (by exact hz.o_intO_4_le_L))
      stk_sc := stk_sc hp md₈.kr (Region.sub_prefix (by exact hz.o_hsWb_le_L hH)) }
  refine ⟨md₈, ua, ?_, by
      rw [e₈]
      exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.repr_keep hH f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj hz (Or.inl (by exact hz.o_stWO_S_le_intO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_intO_4_le_L)) (by rw [u₂.mem]; exact rs₁),
    by rw [e₈, e₃, bytesAt_writeBytes_self' (by rfl) (by decide)]⟩
  rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
    md₃.x20, Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `update` with `INT (k + 1)`. -/
theorem callA_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.AtUpd hH s₀ k s) :
    WP isa (.call H.updN H.updC) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hk' : k * H.D ≤ ol s₀ := Nat.le_of_lt ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hz.z.D0).1 hk)
  refine VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_call hH.stream h.args fun s₁ a₁ r₁ => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_hsS_le_L⟩
      · exact .inl ⟨_, rfl, hWb⟩
  · have := r₁ _ h.repr (by
      rw [h.x1, List.length_append, xorPad_length, VG.Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_length, bytesAt_length])
    rwa [h.int] at this

/-- HMAC's `finalize`'s arguments. -/
theorem finArgs_ok (hH : HashOK H) {k : Nat} {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.block H.finArgs) s (VG.Proof.Pbkdf2.Md.AArch64.Pbk.AtFin hH s₀ k) := by
  have hD := hz.z.DN; have hN := hz.N
  have hB := hz.B_le
  simp only [Hash.finArgs]
  refine wp_addImm (by exact hz.o_stWO_lt_4096) fun s₁ u₁ => wp_addImm (by exact hz.o_st1O_lt_4096) fun s₂ u₂ => wp_addImm (by exact hz.o_B_4_lt_4096) fun s₃ u₃ =>
    wp_addImm (by exact hz.o_uO_lt_4096) fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have m₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  have e₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stk : ∀ {o n : Nat}, o + n ≤ (H.W + H.S) * 8 → (below s₅.sp 16).Disjoint (sR s₀ o n) :=
    fun h => stk_sc hp m₅.kr (part_sub h)
  have fa : FinArgs (H := H) s₅ (A s₀ H.stWO) (A s₀ H.st1O) (s₀.gpr .x3 + BitVec.ofNat 64 (H.P.B + 4))
      (A s₀ H.uO) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) :=
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x1 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
          u₁.other _ (by decide), h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        obtain ⟨r', h', off, e, l⟩ := cov_part hp m₅.kr (o := H.st1O) (n := H.S) (by exact hz.o_st1O_S_le_L)
        exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp m₅.kr (by exact hz.o_stWO_S_le_L)
        · exact cov_part hp m₅.kr (by exact hz.o_uO_D_le_L)
        · exact cov_low hp m₅.kr (by exact hz.o_W8_le_L)
      i_u := part_disj hz (Or.inr (by exact hz.o_st1O_S_le_stWO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_st1O_S_le_L)
      i_o := part_disj hz (Or.inl (by exact hz.o_stWO_S_le_uO)) (by exact hz.o_stWO_S_le_L) (by exact hz.o_uO_D_le_L)
      i_s := low_disj hz (by exact hz.o_W8_le_stWO) (by exact hz.o_stWO_S_le_L)
      u_o := part_disj hz (Or.inl (by exact hz.o_st1O_S_le_uO)) (by exact hz.o_st1O_S_le_L) (by exact hz.o_uO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_st1O) (by exact hz.o_st1O_S_le_L)
      o_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      sp16 := by rw [m₅.kr.sp]; exact hp.sp16
      stk_i := stk (by exact hz.o_stWO_S_le_L)
      stk_u := stk (by exact hz.o_st1O_S_le_L)
      stk_o := stk (by exact hz.o_uO_D_le_L)
      stk_s := stk_sc hp m₅.kr low_sub
      scnw := by have := hp.snw; omega }
  exact ⟨m₅, fa, by rw [e₅]; exact hr⟩

/-- HMAC's `finalize`: `U₁`. -/
theorem callB_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.AtFin hH s₀ k s) :
    WP isa (.call H.hmacFinN H.hmacFin) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.U1 hH s₀ k := by
  have hL := L_lt hz
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hz.z.D0).1 hk
  have hk' := Nat.le_of_lt hkD
  have hsl : sl s₀ + (H.W + H.S) * 8 ≤ 2 ^ 64 := VG.Proof.Pbkdf2.Md.AArch64.Pbk.len_add_le hp.sa_s hp.sanw hp.snw
  refine hfin_call hH hF hFd h.args fun s₁ a₁ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by exact hz.o_stWO_S_le_L⟩
      · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_uO, by exact hz.o_uO_D_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · have hK := VG.Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    exact hpost _ _ hK (by rw [hK, List.length_append, bytesAt_length]; simp [Spec.Pbkdf2.int]; have := hz.o_B_5_le_L; omega)
      (by rw [← List.append_assoc]; exact h.repr)
      (by
        rw [List.length_append, bytesAt_length, show (Spec.Pbkdf2.int (k + 1)).length = 4 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have : sl s₀ = (s₀.gpr .x3).toNat := rfl
        omega)
      h.mid.st.o

/-- `U` copied to `T`, and `iterate`'s arguments. -/
theorem pieceC_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s₇ : State} (m₇ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s₇)
    (hU : bytesAt s₇.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.U1 hH s₀ k) :
    WP isa (.block H.iterArgs) s₇ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.AtIter hH s₀ k) := by
  have hL := L_lt hz
  have hD := hz.z.D0; have hD4 := hz.z.D4; have hDN := hz.z.DN; have hN := hz.N; have hBg := hz.B_ge
  have eD : 4 * (H.D / 4) = H.D := by exact hz.o_4mDd4_eq_D
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hD).1 hk
  have hk' := Nat.le_of_lt hkD
  -- `U` copied to `T`.
  simp only [Hash.iterArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.uO H.tO (H.D / 4)
    ⟨by exact hz.o_uO_mod_4_eq_0, by exact hz.o_uO_4mDd4_le_4096m4⟩ ⟨by exact hz.o_tO_mod_4_eq_0, by exact hz.o_tO_4mDd4_le_4096m4⟩ _ s₇ _
    (fun j hj => by rw [m₇.kr.x23, add_ofNat]; exact in_rw hp hz m₇.kr (by omega_using [hj, hz.o_uO_D_le_L]))
    (fun j hj => by rw [m₇.kr.x23, add_ofNat]; exact in_sc hp hz m₇.kr.wr (by omega_using [hj, hz.o_tO_D_le_L]))
    (by rw [m₇.kr.x23, eD]; exact (part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₈ g₈ rd₈ wr₈ sp₈ c₈ => ?_
  rw [m₇.kr.x23, eD] at c₈
  have f₈ : Frame [sR s₀ H.tO H.D] s₇.mem s₈.mem := by
    rw [c₈]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have m₈ := m₇.write hp hz hH hk' rd₈ wr₈ sp₈ (fun r hr => g₈ r (by rintro rfl; revert hr; decide))
    (o := H.tO) (n := H.D) (by exact hz.o_stWO_le_tO) (by exact hz.o_tO_D_le_L) f₈
  have hU₈ : bytesAt s₈.mem (A s₀ H.uO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D :=
    bytes_keep f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)) (by exact hz.o_D_le_p64)
  have hT₈ : bytesAt s₈.mem (A s₀ H.tO) H.D = bytesAt s₇.mem (A s₀ H.uO) H.D := by
    rw [c₈]; exact bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by exact hz.o_D_lt_p64)
  -- `iterate`'s arguments.
  refine wp_addImm (by exact hz.o_st0O_lt_4096) fun s₉ u₉ => wp_addImm (by exact hz.o_uO_lt_4096) fun s₁₀ u₁₀ => ?_
  have m₁₀ := (m₈.upd u₉ (by decide)).upd u₁₀ (by decide)
  refine wp_ldr (a := A s₀ H.cO) ⟨by exact hz.o_cO_mod_8_eq_0, by exact hz.o_cO_lt_4096m8⟩ (by rw [m₁₀.kr.x23]) (in_rw hp hz m₁₀.kr (by exact hz.o_cO_8_le_L))
    fun s₁₁ u₁₁ => ?_
  have m₁₁ := m₁₀.upd u₁₁ (by decide)
  refine wp_addImm (by exact hz.o_tO_lt_4096) fun s₁₂ u₁₂ => wp_mov fun s₁₃ u₁₃ => WP.block_nil ?_
  have m₁₃ := (m₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)
  have e₁₃ : s₁₃.mem = s₈.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have ia : IterArgs (H := H) s₁₃ (A s₀ H.st0O) (A s₀ H.uO) (BitVec.ofNat 64 (cc s₀ - 1)) (A s₀ H.tO)
      (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) :=
    { x0 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), u₉.gpr, m₈.kr.x23]
      x1 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
          u₉.other _ (by decide), m₈.kr.x23]
      x2 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.mem, u₉.mem, m₈.kr.cW]
      x3 := by rw [u₁₃.other _ (by decide), u₁₂.gpr, m₁₁.kr.x23]
      x4 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), m₁₁.kr.x23]
      cr := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₃.kr (o := H.st0O) (n := 2 * H.S) (by exact hz.o_st0O_2mS_le_L)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
        · obtain ⟨r', h', off, e, l⟩ := cov_part hp m₁₃.kr (o := H.uO) (n := H.D) (by exact hz.o_uO_D_le_L)
          exact ⟨r', List.mem_append_right _ h', off, e, l⟩
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp m₁₃.kr (by exact hz.o_tO_D_le_L)
        · exact cov_low hp m₁₃.kr (by exact hz.o_W8_le_L)
      k_t := part_disj hz (Or.inl (by exact hz.o_st0O_2mS_le_tO)) (by exact hz.o_st0O_2mS_le_L) (by exact hz.o_tO_D_le_L)
      k_s := low_disj hz (by exact hz.o_W8_le_st0O) (by exact hz.o_st0O_2mS_le_L)
      u_t := part_disj hz (Or.inl (by exact hz.o_uO_D_le_tO)) (by exact hz.o_uO_D_le_L) (by exact hz.o_tO_D_le_L)
      u_s := low_disj hz (by exact hz.o_W8_le_uO) (by exact hz.o_uO_D_le_L)
      t_s := low_disj hz (by exact hz.o_W8_le_tO) (by exact hz.o_tO_D_le_L)
      knw := by
        have := hp.snw
        have e : (A s₀ H.st0O).toNat = (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀).toNat + H.st0O := by
          simp only [A, BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (a := H.st0O) (by exact hz.o_st0O_lt_p64), Nat.mod_eq_of_lt (by omega_using [hp.snw, hz.o_st0O_2mS_le_L, hz.o_0_lt_S])]
        rw [e]; omega_using [hp.snw, hz.o_st0O_2mS_le_L]
      scnw := by have := hp.snw; omega }
  exact ⟨m₁₃, ia, by rw [e₁₃, hU₈, hU], by rw [e₁₃, hT₈, hU]⟩

/-- `iterate`: `T_{k+1}`. -/
theorem callC_ok (hH : HashOK H) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.AtIter hH s₀ k s) :
    WP isa (.call H.iterN H.iterate) s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.Tb hH s₀ (k + 1) := by
  have hk' : k * H.D ≤ ol s₀ := Nat.le_of_lt ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hz.z.D0).1 hk)
  refine iter_call hH hI hId h.args fun s₁ a₁ hpost => ⟨?_, ?_⟩
  · exact h.mid.call hp hz hH hk' a₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨_, _, rfl, by exact hz.o_stWO_le_tO, by exact hz.o_tO_D_le_L⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  have hK := VG.Proof.Pbkdf2.Md.AArch64.Pbk.blockKey_length hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have hc : ((BitVec.ofNat 64 (cc s₀ - 1)).setWidth 32).toNat = cc s₀ - 1 := by
    have := ((s₀.gpr .x4).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hO : A s₀ H.st0O + BitVec.ofNat 64 H.S = A s₀ H.st1O := by
    rw [add_ofNat, show H.st0O + H.S = H.st1O by exact hz.o_st0O_S_eq_st1O]
  rw [hpost _ hK h.mid.st.i (hO ▸ h.mid.st.o), hc, h.u, h.t]
  rfl

/-! ## A step: copying `T` out -/

omit hp in
/-- The bytes of `T` the output still needs: `x21 - D` is negative (its top
bit set) exactly when fewer than `D` are left. -/
theorem outLen_ok {hH : HashOK H} {k : Nat} (hol : ol s₀ < 2 ^ 63) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s) :
    WP isa H.outLen s fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧
      t.gpr .x11 = BitVec.ofNat 64 (min (ol s₀ - k * H.D) H.D) ∧ t.mem = s.mem := by
  have hD := hz.z.D0; have hDN := hz.z.DN; have hN := hz.N
  unfold Hash.outLen
  refine WP.seq (wp_movz fun s₁ u₁ => wp_subImm (by exact hz.o_D_lt_4096) fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ =>
    WP.block_nil ?_)
  have m₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have e₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have x11 : s₃.gpr .x11 = BitVec.ofNat 64 H.D := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, movz_ofNat (by exact hz.o_D_lt_p16)]
  have ev : isa.eval (.zero .x .x9) s₃ = some (decide (H.D ≤ ol s₀ - k * H.D)) := by
    change eval (.zero .x .x9) s₃ = _
    rw [eval_zero, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.x21, VG.Proof.Pbkdf2.Md.AArch64.Pbk.shr_beq_zero]
    simp only [Option.some.injEq, decide_eq_decide]
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine WP.ite _ ev (fun hT => WP.block_nil ⟨m₃, ?_, e₃⟩) fun hF => wp_mov fun s₄ u₄ =>
    WP.block_nil ⟨m₃.upd u₄ (by decide), ?_, by rw [u₄.mem, e₃]⟩
  · rw [x11, Nat.min_eq_right (of_decide_eq_true hT)]
  · have := of_decide_eq_false hF
    rw [u₄.gpr, m₃.x21, Nat.min_eq_left (by omega)]

/-- Copying as much of `T_{k+1}` as the output needs, and on to the next block. -/
theorem tail_ok (hH : HashOK H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) (hg : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ k).length = k * H.D) {s : State}
    (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s) (ht : bytesAt s.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.Tb hH s₀ (k + 1)) :
    WP isa (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (k + 1) t ∧ isa.eval (.nonzero .x .x21) t = some (decide (k + 1 ≠ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀)) := by
  have hL := L_lt hz
  have hD := hz.z.D0; have hDN := hz.z.DN; have hN := hz.N
  have hol : ol s₀ < 2 ^ 63 := by have := hp.olD; omega
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hD).1 hk
  have hk1 := VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb (s₀ := s₀) hD (k := k + 1)
  rw [Nat.succ_mul] at hk1
  have hon := hp.onw
  generalize en : min (ol s₀ - k * H.D) H.D = n
  have hn : 0 < n ∧ n ≤ H.D ∧ k * H.D + n ≤ ol s₀ := by omega
  have hdn : VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ (k + 1) = k * H.D + n := by
    show min ((k + 1) * H.D) (ol s₀) = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀) := Offset.sub_base _ hn.2.2
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outLen_ok hz hol h) fun s₁ ⟨m₁, rc₁, e₁⟩ => ?_)
  rw [en] at rc₁
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outLoop_ok (n := n) hn.1 (by omega) (by exact hz.o_tO_lt_4096) rc₁
    (fun j hj => by rw [m₁.kr.x23, add_ofNat]; exact in_rw hp hz m₁.kr (by omega_using [hj, hn.2.1, hz.o_tO_D_le_L]))
    (fun j hj => by
      rw [m₁.x22, add_ofNat]
      exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀, by rw [m₁.kr.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [m₁.kr.x23, m₁.x22]; exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega_using [hn.2.1, hz.o_tO_D_le_L]))).symm))
    fun s₂ c₂ => ?_)
  rw [m₁.kr.x23, m₁.x22] at c₂
  have f₂ : Frame [(⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)] s₁.mem s₂.mem := by
    rw [c₂.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have od : ∀ {X : Region}, Region.Sub X (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀) →
      ∀ r ∈ [(⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ + BitVec.ofNat 64 (k * H.D), n⟩ : Region)], X.Disjoint r := fun hX r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.o_s.sub_left osub).sub_right hX).symm
  have k₂ : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s₂ := m₁.kr.keep c₂.rd c₂.wr c₂.sp (fun r hr => c₂.other r (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_clob r hr)) f₂
    (od (part_sub (by exact hz.o_sv_80_le_L))) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩
  have g₂ : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs, s₂.gpr r = s₁.gpr r := fun r hr => c₂.other r (VG.Proof.Pbkdf2.Md.AArch64.Pbk.eregs_clob r hr)
  refine wp_add fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  have e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have x21 : s₅.gpr .x21 = BitVec.ofNat 64 (ol s₀ - VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ (k + 1)) := by
    rw [u₅.gpr, u₄.other .x21 (by decide), u₄.other .x24 (by decide), u₃.other .x21 (by decide),
      u₃.other .x24 (by decide), g₂ _ (by decide), c₂.x24, m₁.x21, sub_ofNat (by omega), hdn, Nat.sub_sub]
  refine ⟨⟨((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide), ?_, ?_, ?_, x21, ?_, ?_, ?_⟩, ?_⟩
  · rw [e₅]; exact m₁.st.keep hz hH f₂ (od (part_sub (by exact hz.o_st0O_3mS_le_L)))
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), m₁.x19]
    exact (ofNat_succ _).symm
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), m₁.x20]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide), c₂.x24, m₁.x22, add_ofNat,
      hdn]
  · rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.G_succ, List.length_append, hg, ← ht, bytesAt_length, Nat.succ_mul]
  · rw [e₅, hdn, bytesAt_add, bytes_keep f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega)).symm)
      (by omega),
      c₂.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega),
      m₁.outB, VG.Proof.Pbkdf2.Md.AArch64.Pbk.G_succ, ← hg, List.take_length_add_append, ← ht, e₁, ← bytesAt_take _ _ hn.2.1]
  · change eval (.nonzero .x .x21) s₅ = _
    rw [eval_nonzero, x21, ofNat_ne_zero (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega

/-! ## The loop and `pbkdf2` -/

/-- One block of the output. -/
theorem block_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ k s) :
    WP isa H.block s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (k + 1) t ∧ isa.eval (.nonzero .x .x21) t = some (decide (k + 1 ≠ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀)) := by
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hz.z.D0).1 hk
  have hd : VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  have m : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s := ⟨h.kr, h.st, h.x19, h.x20, by rw [h.x21, hd], by rw [h.x22, hd], hb⟩
  unfold Hash.block
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pieceA_ok hp hz hH hk m) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.callA_ok hp hz hH hk h₁) fun s₂ ⟨m₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.finArgs_ok hp hz hH m₂ r₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.callB_ok hp hz hH hF hFd hk h₃) fun s₄ ⟨m₄, u₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pieceC_ok hp hz hH hk m₄ u₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.callC_ok hp hz hH hI hId hk h₅) fun s₆ ⟨m₆, t₆⟩ => ?_)
  exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.tail_ok hp hz hH hk h.glen m₆ t₆

/-- The loop over the blocks of the output: none when `out_len = 0`. -/
theorem loop_ok (hH : HashOK H) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ 0 s)
    (hz0 : isa.eval (.zero .x .x21) s = some (decide (ol s₀ = 0))) :
    WP isa (.ite (.zero .x .x21) (.block []) (.loop H.block (.nonzero .x .x21))) s (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀)) := by
  have hD := hz.z.D0
  refine WP.ite (decide (ol s₀ = 0)) hz0 (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [(VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_zero hD).2 (of_decide_eq_true h0)]; exact h
  · have : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ ≠ 0 := fun e => by simp [(VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_zero hD).1 e] at h0
    exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_loop (Nat.pos_of_ne_zero this) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀)
      (fun k hk t ht => VG.Proof.Pbkdf2.Md.AArch64.Pbk.block_ok hp hz hH hF hFd hI hId hk ht) h

theorem correct (hH : HashOK H) (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hInd : H.hmacInit.aarch64Depth ≤ 1) (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W))
    (hFd : H.hmacFin.aarch64Depth ≤ 1) (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W))
    (hId : H.iterate.aarch64Depth ≤ 1) :
    WP isa H.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hH.SH (H.W + H.S)).post s₀ s' := by
  apply WP.withPreservedV (hc := hH.pbkdf2_keepsV)
  have hD := hz.z.D0; have hW := hz.W
  unfold Hash.pbkdf2
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.entry_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_ok hp hz hH k₁) fun s₂ ⟨k₂, x2₂, x3₂, ka⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.setup_ok hp hz hH hIn hInd k₂ x2₂ x3₂ ka) fun s₃ ⟨k₃, st₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.loopRegs_ok hp hz hH k₃ st₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.loop_ok hp hz hH hF hFd hI hId i₄ z₄) fun s₅ i₅ => ?_)
  have k₅ := i₅.kr
  unfold Hash.exit
  refine WP.mono (restore_ok H.hh k₅.x23 (by show H.W ≤ 1024; exact hz.o_W_le_1024) k₅.saved (in_wr hp k₅)
    (by have : H.S = H.P.N + H.P.B := rfl; have := hz.B_ge; show 8 * H.W + 56 ≤ (H.W + H.S) * 8; exact hz.o_W8_56_le_L))
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hsp, k₅.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hg _ (by decide)
      | exact (ho _ (by decide)).trans (k₅.cs _ (by decide))
  have hdone : VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) = ol s₀ := by
    have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol_le (s₀ := s₀) hD; show min _ _ = _; omega
  have hb := i₅.outB
  rw [hdone] at hb
  show Spec.Pbkdf2.pbkdf2Hmac hH.SH (bytesAt s₀.mem (pw s₀) (pwl s₀)) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀) (cc s₀) (ol s₀) =
    some (bytesAt s'.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀) (ol s₀))
  have hol := hp.olD
  rw [Spec.Pbkdf2.pbkdf2Hmac, hH.hD, Spec.Pbkdf2.pbkdf2, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hm,
    hb]
  rfl

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Pbkdf2CT`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`, constant time

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Pbkdf2CT.lean`): the pieces between the
calls are checked by the taint analysis (`Checks`, `by taint_decide` for each
hash function), each from registers that the correctness proof fixes to public
values (`KE`, `Mid`, `KR`): they are the same in two runs that agree on the
public arguments. The calls are constant time by their callees' proofs
(`RelCT.call`, with arguments the correctness proof fixes to the same values),
and the branches and the loop go the same way in both runs, by the facts the
correctness proof gives about the registers they test.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG rel_taint rel_wp)
open VG.Proof.MdStream.AArch64 (wp_lsr wp_subImm)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-- The public arguments `entry` reads (`c`, only half public, it only
stores). -/
abbrev entryRegs : List Reg := [.x0, .x1, .x2, .x3, .x5, .x6, .x7]

/-- The taint checks of the pieces of `pbkdf2` between its calls, branches
and loops. -/
structure Checks (H : Hash) : Prop where
  entry : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.entryRegs) (.block H.entry) hc).isSome = true
  hk1 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.hkInit) hc).isSome = true
  hk3 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.hkUpd) hc).isSome = true
  hk5 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.hkFin) hc).isSome = true
  hk7 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.hkKey) hc).isSome = true
  keyShr : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.keyShr) hc).isSome = true
  keySub : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.keySub) hc).isSome = true
  short : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block Hash.short) hc).isSome = true
  su1 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.initArgs) hc).isSome = true
  su3 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.saltArgs) hc).isSome = true
  loopRegs : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.loopRegs) hc).isSome = true
  pieceA : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.intArgs) hc).isSome = true
  finArgs : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.finArgs) hc).isSome = true
  pieceC : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (.block H.iterArgs) hc).isSome = true
  tail : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub)
    (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) hc).isSome = true
  exit : ∃ hc, (Taint.check taint (Taint.ofRegs [.x23]) (.block H.exit) hc).isSome = true

/-- The public arguments are the same (`c` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : (s₀.gpr .x4).setWidth 32 = (s₀'.gpr .x4).setWidth 32
  x5 : s₀.gpr .x5 = s₀'.gpr .x5
  x6 : s₀.gpr .x6 = s₀'.gpr .x6
  x7 : s₀.gpr .x7 = s₀'.gpr .x7
  sp : s₀.sp = s₀'.sp

/-! ## The key's branches, one run at a time -/

section
variable {s₀ : State} (hz : PSizes H)
include hz

theorem keyShr_ok {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) :
    WP isa (.block H.keyShr) s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ < H.P.B)) := by
  unfold Hash.keyShr
  exact wp_lsr (VG.Proof.Pbkdf2.Md.AArch64.Pbk.log2_B hz).2 fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_shr hz h u₁⟩

theorem keySub_ok {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) :
    WP isa (.block H.keySub) s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ = H.P.B)) := by
  have hB := hz.B_le
  unfold Hash.keySub
  exact wp_subImm (by omega) fun s₂ u₂ => WP.block_nil ⟨h.upd u₂ (by decide), VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_sub h u₂ (by omega)⟩

end

section
variable {s₀ s₀' : State} (hq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PubEq s₀ s₀')
include hq

/-! ## What agrees in the two runs -/

theorem scr_eq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀' = VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀ := hq.x7.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀' + _ = VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀ + _; rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq]
theorem pw_eq : pw s₀' = pw s₀ := hq.x0.symm
theorem pwl_eq : pwl s₀' = pwl s₀ := by show (s₀'.gpr .x1).toNat = _; rw [← hq.x1]
theorem salt_eq : salt s₀' = salt s₀ := hq.x2.symm
theorem sl_eq : sl s₀' = sl s₀ := by show (s₀'.gpr .x3).toNat = _; rw [← hq.x3]
theorem cc_eq : cc s₀' = cc s₀ := by show ((s₀'.gpr .x4).setWidth 32).toNat = _; rw [← hq.x4]
theorem out_eq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀' = VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀ := hq.x5.symm
theorem ol_eq : ol s₀' = ol s₀ := by show (s₀'.gpr .x6).toNat = _; rw [← hq.x6]
theorem nb_eq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀' = VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ := by show (ol s₀' + H.D - 1) / H.D = _; rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol_eq hq]
theorem kp_eq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀' = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pw s₀' else A s₀' H.hkO) = _; rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq]
theorem kl_eq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀' = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pwl s₀' else H.D) = _; rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl_eq hq]

theorem kr_agree {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ [Reg.x23], s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [h.x23, h'.x23, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq]

theorem ke_agree {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub, s.gpr r = s'.gpr r := by
  refine ⟨(VG.Proof.Pbkdf2.Md.AArch64.Pbk.kr_agree hq h.kr h'.kr).1, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw_eq hq]
  · rw [h.x20, h'.x20, hq.x1]
  · rw [h.x21, h'.x21, VG.Proof.Pbkdf2.Md.AArch64.Pbk.salt_eq hq]
  · rw [h.x22, h'.x22, hq.x3]
  · exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kr_agree hq h.kr h'.kr).2 _ (by simp)

theorem mid_agree {hH : HashOK H} {k : Nat} {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k s') :
    s.sp = s'.sp ∧ ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub, s.gpr r = s'.gpr r := by
  refine ⟨(VG.Proof.Pbkdf2.Md.AArch64.Pbk.kr_agree hq h.kr h'.kr).1, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19]
  · rw [h.x20, h'.x20, hq.x3]
  · rw [h.x21, h'.x21, VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol_eq hq]
  · rw [h.x22, h'.x22, VG.Proof.Pbkdf2.Md.AArch64.Pbk.out_eq hq]
  · exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kr_agree hq h.kr h'.kr).2 _ (by simp)

end

/-! ## The pieces in two runs -/

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hp' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀') (hz : PSizes H)
  (hq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Checks H)
include hH hp hp' hz hq hc

omit hH in
theorem entry_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.entry)
    fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s' :=
  rel_taint VG.Proof.Pbkdf2.Md.AArch64.Pbk.entryRegs (fun s s' e e' => by
      rw [e, e']
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hq.x0, hq.x1, hq.x2, hq.x3, hq.x5, hq.x6, hq.x7]) hc.entry
    (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.entry_ok hp hz) (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.entry_ok hp' hz)

/-- Hashing a password longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') => VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO)
    (G' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧ t.gpr .x0 = A s₀' H.stWO) VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub ag hc.hk1
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk1_ok hz h) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) σ₀ → VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.stream.S⟩] s.wr :=
    fun hp h => Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega)
  have c₂ := rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ s.gpr .x0 = A s₀ H.stWO) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s' ∧ s'.gpr .x0 = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i, i', (VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq h.1.1 h.2.1).1⟩)
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk2_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk3_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk5_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], (VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq k k').1⟩)
        (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.x1], (VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq k k').1⟩)
        (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') H.key
    fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ s.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ ∧ (s.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ ∧
        VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀)) ∧
      (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s' ∧ s'.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀' ∧ (s'.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀' ∧
        VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀' s'.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀')) := by
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') => VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq h h'
  obtain ⟨_, hs⟩ := hc.short
  have short : ∀ {P : State → State → Prop}, (∀ s s', P s s' → VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') →
      RelCT isa P (.block Hash.short) fun _ _ => True := fun hP =>
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq (hP _ _ h).1 (hP _ _ h).2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hs
  have ite : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') H.key fun _ _ => True := by
    unfold Hash.key
    have r₁ := rel_taint
      (G := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ < H.P.B)))
      (G' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀' < H.P.B)))
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub ag hc.keyShr (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.keyShr_ok hz h) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.keyShr_ok hz h)
    refine r₁.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)
    have r₂ := rel_taint
      (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t) (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t)
      (G := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ = H.P.B)))
      (G' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀' = H.P.B)))
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub ag hc.keySub (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.keySub_ok hz h) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.keySub_ok hz h)
    refine (r₂.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  exact (ite.wp fun s s' h => ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_ok hp hz hH h.1, VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_ok hp' hz hH h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- HMAC's states, and the inner one after the salt. -/
theorem setup_rel (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hInd : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ s.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ ∧ (s.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ ∧
        VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀)) ∧
      (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s' ∧ s'.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀' ∧ (s'.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀' ∧
        VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀' s'.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀'))) H.setup
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ s.mem) ∧ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s' ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀' s'.mem) := by
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s') => VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq h h'
  unfold Hash.setup
  have r₁ := rel_taint
    (F := fun s => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ s.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀ ∧ (s.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀ ∧
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀))
    (F' := fun s => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s ∧ s.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀' ∧ (s.gpr .x3).toNat = VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀' ∧
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀' s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀'))
    (G := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀) ∧
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀ t.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀))
    (G' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧
      InitArgs (H := H) t (A s₀' H.st0O) (A s₀' H.st1O) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀') ∧
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.KeyAt hH s₀' t.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp H s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl H s₀'))
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => ag s s' h.1 h'.1) hc.su1
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su1_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su1_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  have r₃ := rel_taint (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) Spec.Hmac.opad))
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' t ∧
      hH.SH.Repr t.mem (A s₀' H.st0O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀') Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀' H.st1O) (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀') Spec.Hmac.opad)) VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub
    (fun s s' h h' => ag s s' h.1 h'.1) hc.su3
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su3_ok hp hz hH h.1 h.2.1 h.2.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su3_ok hp' hz hH h.1 h.2.1 h.2.2)
  refine r₁.seq (RelCT.seq ?_ (r₃.seq ?_))
  · exact rel_wp (hinit_rel hH hIn fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.kp_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.kl_eq hq] at a'
        exact ⟨a, a', (VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq k k').1⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su2_ok hp hz hH hIn hInd h.1 h.2.1 h.2.2)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su2_ok hp' hz hH hIn hInd h.1 h.2.1 h.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
        obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
        rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.salt_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.sl_eq hq] at a'
        exact ⟨a, a', by rw [i, i'], (VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq k k').1⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.su4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)

end

/-! ## The blocks of the output -/

theorem inv_mid {hH : HashOK H} {s₀ : State} (hz : PSizes H) {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) {s : State}
    (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ k s) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s := by
  have hkD : k * H.D < ol s₀ := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lt_nb hz.z.D0).1 hk
  have hd : VG.Proof.Pbkdf2.Md.AArch64.Pbk.done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  exact ⟨h.kr, h.st, h.x19, h.x20, by rw [h.x21, hd], by rw [h.x22, hd], hb⟩

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LI (hH : HashOK H) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  n ≤ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ ∧ 0 < n ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - n) s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - n) s'

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hp' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀') (hz : PSizes H)
  (hq : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PubEq s₀ s₀') (hc : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Checks H)
  (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) (hFd : H.hmacFin.aarch64Depth ≤ 1)
  (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hId : H.iterate.aarch64Depth ≤ 1)
include hH hp hp' hz hq hc hF hFd hI hId

theorem block_mid_rel {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) (hg : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀ k).length = k * H.D)
    (hg' : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.G hH s₀' k).length = k * H.D) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k s') H.block fun _ _ => True := by
  have hk' : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀' := by rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_eq hq]; exact hk
  have ag := fun (s s' : State) (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s) (h' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k s') => VG.Proof.Pbkdf2.Md.AArch64.Pbk.mid_agree hq h h'
  have msp : ∀ {s s' : State}, VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k s → VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k s' → s.sp = s'.sp :=
    fun h h' => (VG.Proof.Pbkdf2.Md.AArch64.Pbk.mid_agree hq h h').1
  unfold Hash.block
  have pA := rel_taint VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub ag hc.pieceA (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.pieceA_ok hp hz hH hk h)
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.pieceA_ok hp' hz hH hk' h)
  have fA := rel_taint
    (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧ hH.SH.Repr t.mem (A s₀ H.stWO)
      (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀) Spec.Hmac.ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k t ∧ hH.SH.Repr t.mem (A s₀' H.stWO)
      (Spec.Hmac.xorPad (VG.Proof.Pbkdf2.Md.AArch64.Pbk.K0 hH s₀') Spec.Hmac.ipad ++ VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltB s₀' ++ Spec.Pbkdf2.int (k + 1)))
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => ag s s' h.1 h'.1) hc.finArgs
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.finArgs_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.finArgs_ok hp' hz hH h.1 h.2)
  have pC := rel_taint
    (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.U1 hH s₀ k)
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.uO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.U1 hH s₀' k)
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => ag s s' h.1 h'.1) hc.pieceC
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.pieceC_ok hp hz hH hk h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.pieceC_ok hp' hz hH hk' h.1 h.2)
  have tl := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.Tb hH s₀ (k + 1))
    (F' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.tO) H.D = VG.Proof.Pbkdf2.Md.AArch64.Pbk.Tb hH s₀' (k + 1))
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => ag s s' h.1 h'.1) hc.tail
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.tail_ok hp hz hH hk hg h.1 h.2) fun _ _ => trivial)
    (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.Pbk.tail_ok hp' hz hH hk' hg' h.1 h.2) fun _ _ => trivial)
  refine (pA.seq (RelCT.seq ?_ (fA.seq (RelCT.seq ?_ (pC.seq (RelCT.seq ?_ tl)))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq] at x
        exact ⟨a.args, x, by rw [a.x1, a'.x1, VG.Proof.Pbkdf2.Md.AArch64.Pbk.sl_eq hq], msp a.mid a'.mid⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.callA_ok hp hz hH hk h) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.callA_ok hp' hz hH hk' h)
  · exact rel_wp (hfin_rel hH hF fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, ← hq.x3, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.callB_ok hp hz hH hF hFd hk h) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.callB_ok hp' hz hH hF hFd hk' h)
  · exact rel_wp (iter_rel hH hI fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.A_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.cc_eq hq, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.callC_ok hp hz hH hI hId hk h) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.callC_ok hp' hz hH hI hId hk' h)

theorem block_rel {k : Nat} (hk : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ k s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' k s') H.block fun s s' =>
      (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (k + 1) s ∧ isa.eval (.nonzero .x .x21) s = some (decide (k + 1 ≠ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀))) ∧
      (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' (k + 1) s' ∧ isa.eval (.nonzero .x .x21) s' = some (decide (k + 1 ≠ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀'))) := by
  have hk' : k < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀' := by rw [VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_eq hq]; exact hk
  intro s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂
  refine ((((VG.Proof.Pbkdf2.Md.AArch64.Pbk.block_mid_rel hH hp hp' hz hq hc hF hFd hI hId hk h.1.glen h.2.glen).mono
    (P' := fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ k s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' k s') (fun _ _ h => ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.inv_mid hz hk h.1, VG.Proof.Pbkdf2.Md.AArch64.Pbk.inv_mid hz hk' h.2⟩)
    fun _ _ h => h).wp fun s s' h => ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.block_ok hp hz hH hF hFd hI hId hk h.1,
      VG.Proof.Pbkdf2.Md.AArch64.Pbk.block_ok hp' hz hH hF hFd hI hId hk' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2)
    _ _ _ _ _ _ h e₁ e₂

theorem step_rel (n : Nat) :
    RelCT isa (VG.Proof.Pbkdf2.Md.AArch64.Pbk.LI hH s₀ s₀' n) H.block fun s s' =>
      isa.eval (.nonzero .x .x21) s = isa.eval (.nonzero .x .x21) s' ∧
      (isa.eval (.nonzero .x .x21) s = some false → VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀') s') ∧
      (isa.eval (.nonzero .x .x21) s = some true → ∃ m < n, VG.Proof.Pbkdf2.Md.AArch64.Pbk.LI hH s₀ s₀' m s s') := by
  by_cases hn : n ≤ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ ∧ 0 < n
  · have hk : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - n < VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ := by omega
    refine ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.block_rel hH hp hp' hz hq hc hF hFd hI hId hk).mono (P' := VG.Proof.Pbkdf2.Md.AArch64.Pbk.LI hH s₀ s₀' n)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e := VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_eq (H := H) hq
    rw [z, z', e]
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - n + 1 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ := by simpa using hf
      rw [hl] at i i'
      exact ⟨i, i'⟩
    · have hl : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - n + 1 ≠ VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ := by simpa using ht
      have e' : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - (n - 1) = VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ - n + 1 := by omega
      exact ⟨n - 1, by omega, by omega, by omega, e' ▸ i, e' ▸ i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ 0 s ∧ isa.eval (.zero .x .x21) s = some (decide (ol s₀ = 0))) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' 0 s' ∧ isa.eval (.zero .x .x21) s' = some (decide (ol s₀' = 0))))
      (.ite (.zero .x .x21) (.block []) (.loop H.block (.nonzero .x .x21)))
      fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀') s' := by
  have hD := hz.z.D0
  have e := VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_eq (H := H) hq; have eo := VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol_eq hq
  refine RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, eo]) ?_ ?_
  · refine RelCT.block_nil fun s s' h => ?_
    have h0 : ol s₀ = 0 := by have := h.1.1.2.symm.trans h.2; simpa using this
    rw [e, (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_zero hD).2 h0]
    exact ⟨h.1.1.1, h.1.2.1⟩
  · refine (RelCT.loop (M := isa) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.LI hH s₀ s₀') (VG.Proof.Pbkdf2.Md.AArch64.Pbk.step_rel hH hp hp' hz hq hc hF hFd hI hId)
      (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have h0 : ol s₀ ≠ 0 := by have := h.1.1.2.symm.trans h.2; simpa using this
    have : VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀ ≠ 0 := fun x => h0 ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb_zero hD).1 x)
    refine ⟨Nat.le_refl _, Nat.pos_of_ne_zero this, ?_, ?_⟩ <;> rw [Nat.sub_self]
    exacts [h.1.1.1, h.1.2.1]

theorem ct (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hInd : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.pbkdf2 fun _ _ => True := by
  unfold Hash.pbkdf2
  have lr := rel_taint (F := fun s => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀ s.mem)
    (F' := fun s => VG.Proof.Pbkdf2.Md.AArch64.Pbk.KE (H := H) s₀' s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.States hH s₀' s.mem)
    (G := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀ = 0)))
    (G' := fun t => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀' = 0)))
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.epub (fun s s' h h' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.ke_agree hq h.1 h'.1) hc.loopRegs
    (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.loopRegs_ok hp hz hH h.1 h.2) (fun _ h => VG.Proof.Pbkdf2.Md.AArch64.Pbk.loopRegs_ok hp' hz hH h.1 h.2)
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.Inv hH s₀' (VG.Proof.Pbkdf2.Md.AArch64.Pbk.nb H s₀') s') (.block H.exit)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x23]) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := VG.Proof.Pbkdf2.Md.AArch64.Pbk.kr_agree hq h.1.kr h.2.kr
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hx
  exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.entry_rel hp hp' hz hq hc).seq ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.key_rel hH hp hp' hz hq hc).seq
    ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.setup_rel hH hp hp' hz hq hc hIn hInd).seq
      (lr.seq ((VG.Proof.Pbkdf2.Md.AArch64.Pbk.loop_rel hH hp hp' hz hq hc hF hFd hI hId).seq ex))))

end

/-- `pbkdf2` is verified against `pbkG`, given the taint checks and the
proofs of the functions it calls. -/
theorem verified {H : Hash} (hH : HashOK H) (hc : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Checks H)
    (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hInd : H.hmacInit.aarch64Depth ≤ 1)
    (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) (hFd : H.hmacFin.aarch64Depth ≤ 1)
    (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hId : H.iterate.aarch64Depth ≤ 1)
    (hsat : ∃ s, (pbkG hH.SH (H.W + H.S)).pre s) :
    Verified AArch64.target H.pbkdf2 (pbkG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.AArch64.Pbk.correct (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pre_of hH hs) hH.psizes hH hIn hInd hF hFd hI hId,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
  exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.ct hH (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pre_of hH h₁) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pre_of hH h₂) hH.psizes ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hc hF hFd hI hId
    hIn hInd _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.HmacFinInner`. -/
section

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize` up to the inner digest

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacFinInner.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) starts by saving our caller's registers and
our return address (`pro_ok`) and finalizing the inner state into `scratch`
with the streaming `finalize` (`fin1Args_ok`, `finCall_ok`): what holds from
the prologue on (`KR`), and that call in two runs (`fin_rel'`). The rest is
`Proof/Pbkdf2/Md/AArch64/HmacFin.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Impl.MdStream.AArch64 (mov)
open VG.Proof.Pbkdf2.Md.AArch64.Calls
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub off_disj off_disj0 covers_one sub_of_off sub_of_self)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt sub_offset contains_offset Upd wp_mov wp_movz wp_addImm)
open Spec.Sha256 (bytesAt)

variable {H : Stream} (hH : StreamOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev outer : Addr := s₀.gpr .x1
abbrev op : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀, H.S⟩
abbrev outerR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outer s₀, H.S⟩
abbrev opR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀, H.D⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀, 8 * sc⟩
abbrev stkR : Region := below s₀.sp 16
/-- Where the digests go. -/
abbrev T : Addr := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H) s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H) s₀)
  i_p : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H) s₀)
  i_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀)
  o_p : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H) s₀)
  o_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀)
  p_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀)
  stk_o : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H) s₀)
  stk_p : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H) s₀)
  stk_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀)
  nw : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 134
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (saveR H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact VG.Proof.MdStream.AArch64.sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.tR (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact VG.Proof.MdStream.AArch64.sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.calR hH s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Stream.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.calR hH s₀).Disjoint (saveR H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact off_disj0 (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 56) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.calR hH s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj0 (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (m := hH.Wb) (b := 8 * H.W + 56) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (a := 8 * H.W) (m := 56) (b := 8 * H.W + 56) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀
  x20 : s.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outer s₀
  x21 : s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀
  x23 : s.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x21, .x23, .x25, .x26, .x27, .x28]

theorem untouched_kregs : ∀ r ∈ untouched, r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs := by decide
theorem kregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem kregs_clob : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs, r ∉ clob := by decide

theorem KR.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)).Disjoint r) : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.untouched_kregs r hr)).trans (h.cs r hr), h.saved.frame H hf hs⟩

theorem KR.regs {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem KR.upd {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs) {v : BitVec 64}
    (u : Upd s s' d v) : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s' :=
  h.regs u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

theorem KR.call {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws ++ [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀], (saveR H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)).Disjoint r) : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [h.sp] at f
  exact h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kregs_pres r hr).2) f hs

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H) sc s₀)
include hp

theorem wr_mem : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s ∧ s.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ ∧
    s.gpr .x2 = s₀.gpr .x2 ∧ Frame [saveR H (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)] s₀.mem s.mem := by
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Stream.buf] at this; omega_nat
  refine save_ok H (scr := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) rfl (Nat.le_trans hp.hW (by decide)) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    fun r hr => k r (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide)
      (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide),
    hm ▸ sv₁⟩, k _ (by decide) (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide) (by decide), hm ▸ f₁⟩

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ t) (h0 : t.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀)
    (h2 : t.gpr .x2 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (h3 : t.gpr .x3 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) :
    VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) := by
  have hwb := hH.hWb; have hf := hp.fits; simp only [Stream.buf] at hf
  obtain ⟨sR, iR, _⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.wr_mem hp
  exact
    { x0 := h0, x2 := h2, x3 := h3
      cw := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.t_sub hp)
      st_sc := hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cal_sub hH hp)
      o_sc := (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cal_t hH hp).symm
      sp16 := by rw [hk.sp]; exact hp.sp16
      stk_st := by rw [hk.sp]; exact hp.stk_i
      stk_o := by rw [hk.sp]; exact hp.stk_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.t_sub hp)
      stk_sc := by rw [hk.sp]; exact hp.stk_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cal_sub hH hp) }

theorem buf_lt : H.buf < 4096 := by
  have := hp.hW; simp only [Stream.buf]; omega_nat

/-- The first call's arguments: the count from `x2`. -/
theorem fin1Args_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s) (h0 : s.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) {c : BitVec 64}
    (h2 : s.gpr .x2 = c) :
    WP isa (.block ([] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr))) s fun t =>
      VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addImm (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.buf_lt hp) fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  have k₃ : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine ⟨k₃, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.finArgs hH hp k₃ ?_ ?_ ?_, ?_, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hk.x23]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2]

theorem finCall_ok {t : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ t) (ha : VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', VecKept t s' → VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s' → Frame [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.tR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.calR hH s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.sp] at f
    refine hQ s' ha'.vec (hk.call ha' ?_) f hpost
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp)
    · exact VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_t hp
    · exact (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp)

end

/-! ## In two runs -/

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x23]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Stream) : List Instr :=
  [] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr)

variable {sc : Nat}
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H) sc s₀) (hp' : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H) sc s₀') (hq : VG.Proof.Pbkdf2.Md.AArch64.Calls.PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : VG.Proof.Pbkdf2.Md.AArch64.Calls.PubEq s₀ s₀') (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn, hq.x0]
  · rw [h.x20, h'.x20, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outer, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outer, hq.x1]
  · rw [h.x21, h'.x21, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op, hq.x3]
  · rw [h.x23, h'.x23, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr, hq.x4]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀ ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ :=
  ⟨hq.x0.symm, by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm⟩

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀' t ∧
      VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀') (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀') (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀') ∧ t.gpr .x1 = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.eqs hq
  have ha := rel_taint (G := fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) ∧
      t.gpr .x1 = c)
    (G' := fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H) s₀' t ∧ VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) ∧ t.gpr .x1 = c)
    VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (o := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H) s₀) (sc := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.finCall_ok hH hp k a fun _ _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ _ k' _ _ => k'))

end VG.Proof.Pbkdf2.Md.AArch64.HmacFin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.HmacFin`. -/
section

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize`

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) starts by finalizing the inner state into
`scratch` (`Proof/Pbkdf2/Md/AArch64/HmacFinInner.lean`); then it computes the outer hash with one compression, as `iterate`
does (`Proof/Pbkdf2/AArch64/Iterate.lean`): it writes the outer hash value
over the inner state's and, into its buffer, the inner digest and the padding
(`finMid`, `mid_ok`), compresses that block (`cmp_ok`) and writes the digest
of the result to `out` (`finOut`, `out_ok`). That this is the outer hash is
`Md.Link.hash_block`. Everything up to the inner digest is
`HmacFinInner.lean`'s, for the hash function's streaming functions
(`HashOK.stream`);
constant time likewise, from the taint checks of the pieces between the calls
(`Checks`) and the compression function's own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream.AArch64 (add_ofNat wp_mov wp_addImm)
open VG.Impl.MdStream.AArch64 (compressAt compressWith mov)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok padLen_ok padLen_keepsV CallOk compressAt_ok compressAt_rel)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (finG FinArgs rel_taint rel_wp fin_rel restore_ok saveR SavedRegs VecKept
  savedRegs repr_keep PubEq args untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The registers the code after the inner digest keeps public: `inner`, the
block (its buffer), `scratch` and `out`. -/
abbrev oregs : List Reg := [.x19, .x21, .x23, .x24]

/-- The registers `KO` fixes. -/
abbrev koregs : List Reg := [.x19, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs) (.block (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacFin.oregs) (.block H.finOut) hc).isSome = true

/-- The block: the inner state's buffer. -/
abbrev blk (H : Hash) (s₀ : State) : Addr := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 H.P.N

/-- What holds from the outer block on: as `KR`, but `outer` is no longer
needed, and `out` is in `x24`. -/
structure KO (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀
  x23 : s.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀
  x24 : s.gpr .x24 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.stream (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) s₀ s.mem

theorem untouched_ko : ∀ r ∈ untouched, r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.koregs := by decide

theorem KO.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.koregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.stream (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)).Disjoint r) : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19, (hg _ (by simp)).trans h.x23,
    (hg _ (by simp)).trans h.x24, fun r hr => (hg r (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.untouched_ko r hr)).trans (h.cs r hr),
    h.saved.frame H.stream hf hs⟩

omit hH in
/-- The end: `abiPreserved`, from `KO` and `restore`. -/
theorem abi_of {s₀ s s' : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s) (hsp : s'.sp = s.sp) (hv : VecKept s₀ s')
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) (ho : ∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, by rw [hsp, hk.sp], hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hg _ (by decide)
    | exact (ho _ (by decide)).trans (hk.cs _ (by decide))

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.P.L % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.D + 4 ≤ H.P.B - H.P.L ∧
    0 < H.D ∧ H.D ≤ H.P.N ∧ H.P.N + H.P.L ≤ H.P.B ∧ H.P.B ≤ 128 ∧ H.P.so % 8 = 0 ∧
    H.P.so + 104 + H.P.N ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 ∧ H.P.so + 104 + H.P.N ≤ 4096 := by
  have := hH.sizes.N4; have := hH.sizes.D4; have := hH.sizes.L4; have := hH.sizes.pad; have := hH.sizes.D0
  have := hH.sizes.DN; have := hH.sizes.NL; have hH_B_le := hH.B_le; have := hH.sizes.dims.so; have hH_N_le := hH.N_le
  have hp_nw := hp.nw; have hp_hS := hp.hS
  have : H.P.md.so = H.P.so := rfl
  have : H.P.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega_using [h]
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hb : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 56 := rfl
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  omega

omit hH hp in
/-- The ranges of the inner state, which holds the hash value and the block. -/
theorem in_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H.stream) s₀) :=
  Offset.sub_base _ h

omit hH in
theorem save_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (saveR H.stream (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)).Disjoint ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp)).sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.in_inR h)

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it; `x20` = `scratch`, `x24` = `out`, and the
block's address in `x21` and `x1`. -/
theorem mid_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ t ∧ t.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ ∧ t.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ ∧
      t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ ∧
      (∀ i < H.P.N, t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 i) = s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) H.D = bytesAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H.stream) s₀) H.D ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.md.tailPad H.D := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, -, h8, hSB, h4k⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have hbuf : H.stream.buf % 4 = 0 ∧ H.stream.buf + H.P.N ≤ 8 * sc ∧ H.stream.buf + H.P.N ≤ 4096 := by
    have : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 56 := rfl
    have : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
    omega
  clear h4k
  have eN : 4 * (H.P.N / 4) = H.P.N := by omega
  have eD : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  obtain ⟨sR, iR, _⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.wr_mem hp
  have oR : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have tsub : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H.stream) s₀, H.D⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀) := Offset.sub_base _ (by omega_using [hbuf, hDN])
  simp only [Hash.finMid, Hash.copy32, List.append_assoc]
  refine copy32_ok (src := .x20) (dst := .x19) (by decide) (by decide) 0 0 (H.P.N / 4) ⟨rfl, by omega_using [hB, hNL]⟩
    ⟨rfl, by omega⟩ _ s _
    (fun j hj => by
      rw [hk.x20, add_ofNat]
      exact ⟨_, oR, Offset.contains_base _ (by omega_using [hj, hS]) (by omega_using [hj, hB, hNL])⟩)
    (fun j hj => by
      rw [hk.x19, add_ofNat, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hk.x20, hk.x19, eN]
      exact hp.i_o.symm.sep (Offset.contains_base _ (by omega_using [hS]) (by omega))
        (Offset.contains_base _ (by omega_using [hS]) (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [hk.x20, hk.x19, eN, z, z] at m₁
  have x23 : s₁.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ := by rw [g₁ _ (by decide), hk.x23]
  have x19 : s₁.gpr .x19 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ := by rw [g₁ _ (by decide), hk.x19]
  refine copy32_ok (src := .x23) (dst := .x19) (by decide) (by decide) H.stream.buf H.P.N (H.D / 4)
    ⟨by omega_using [hbuf], by omega_using [hbuf, hDN]⟩ ⟨hN4, by omega_using [hB, hNL, hpad]⟩ _ s₁ _
    (fun j hj => by
      rw [x23, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega_using [hj, hbuf, hDN]) (by omega_using [hj, hbuf, hDN])⟩)
    (fun j hj => by
      rw [x19, add_ofNat, wr₁, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [hj, hS, hpad]) (by omega_using [hj, hB, hNL, hpad])⟩)
    (by
      rw [x23, x19, eD]
      exact hp.i_s.symm.sep (Offset.contains_base _ (by omega) (by omega_using [hbuf]))
        (Offset.contains_base _ (by omega_using [hS, hpad]) (by omega_using [hB, hNL])))
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  rw [x23, x19, eD] at m₂
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => wp_addImm (by omega_using [hB, hNL]) fun s₄ u₄ => wp_mov fun s₅ u₅ => ?_
  have x21₅ : s₅.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), x19]
  have G₅ : ∀ r, r ≠ .x9 → r ≠ .x20 → r ≠ .x21 → r ≠ .x24 → s₅.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h2, u₄.other r h3, u₃.other r h4, g₂ r h1]
  refine padLen_ok hH.shape (hH.lenOk _ (by omega_using [hB, hpad])) hD4 hL4 hB4 hpad hB (s := s₅) x21₅
    (by rw [G₅ _ (by decide) (by decide) (by decide) (by decide), x19, add_ofNat,
      show H.P.N + (H.P.B - H.P.L) = H.P.N + H.P.B - H.P.L by omega_using [hpad]])
    (fun a n h' => by
      rw [u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr, add_ofNat]
      exact ⟨_, iR, Offset.contains_base _ (by omega_using [h', hS]) (by omega_using [h', hB, hNL])⟩) fun s₆ g₆ rd₆ wr₆ sp₆ f₆ p₆ d₆ => ?_
  refine wp_mov fun s₇ u₇ => WP.block_nil ?_
  have G : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x22 → r ≠ .x1 → s₇.gpr r = s₅.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other r h4, g₆ r h1 h2 h3]
  have hm : s₇.mem = s₆.mem := u₇.mem
  have f₁ : Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀, H.P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₂ : Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  rw [f₅] at f₆ d₆
  have fI : Frame [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H.stream) s₀] s.mem s₇.mem := by
    rw [hm]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₆.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [hS])⟩
    · exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.in_inR (by omega_using [hpad])⟩
    · exact ⟨_, List.mem_singleton_self _, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.in_inR (by omega)⟩
  have Gk : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x22 → r ≠ .x1 → r ≠ .x20 → r ≠ .x21 → r ≠ .x24 →
      s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    rw [G r h1 h2 h3 h4, G₅ r h1 h5 h6 h7, g₁ r h1]
  have hu : ∀ r ∈ untouched, r ≠ .x9 ∧ r ≠ .x12 ∧ r ≠ .x22 ∧ r ≠ .x1 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x24 := by
    decide
  refine ⟨⟨by rw [u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁, hk.rd],
      by rw [u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr],
      by rw [u₇.sp, sp₆, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁, hk.sp],
      by rw [Gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk.x19],
      by rw [Gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk.x23],
      by rw [G _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, g₂ _ (by decide), g₁ _ (by decide), hk.x21],
      fun r hr => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hu r hr
        rw [Gk r h1 h2 h3 h4 h5 h6 h7, hk.cs r hr],
      hk.saved.frame H.stream fI (by
        simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp))⟩,
    by rw [G _ (by decide) (by decide) (by decide) (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hk.x23],
    by rw [G _ (by decide) (by decide) (by decide) (by decide), x21₅],
    by rw [u₇.gpr, g₆ _ (by decide) (by decide) (by decide), x21₅], fun i hi => ?_, ?_, by rw [hm]; exact p₆⟩
  · -- The hash value: the outer one, which the later pieces keep.
    have hd : ∀ {a n : Nat}, H.P.N ≤ a → a + n ≤ H.P.N + H.P.B →
        ∀ r ∈ [(⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 a, n⟩ : Region)], Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀, H.P.N⟩ r := fun ha hn => by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ ha (by omega_using [hn, hB, hNL])
    rw [hm, f₆.bytes (R := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega)) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      f₂.bytes (R := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega_using [hpad])) (by show H.P.N ≤ 2 ^ 64; omega_using [hB, hNL]) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hB, hNL]),
      bytesAt_getD' _ _ hi]
  · -- The inner digest.
    rw [hm, d₆, m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hB, hpad])]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm.sub_right (Region.sub_prefix (by omega_using [hS]))) (by omega_using [hB, hpad])

/-- What the call of the compression function needs. -/
theorem callOk {t : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ t) (h20 : t.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (h1 : t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) :
    CallOk t H.P.N H.P.B H.P.so (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, _⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.wr_mem hp
  have z : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ := BitVec.add_zero _
  have hv : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀, H.P.N⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H.stream) s₀) := Region.sub_prefix (by omega_using [hS])
  have hb : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀, H.P.B⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H.stream) s₀) := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.in_inR (by omega)
  have hs : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀, H.P.so⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scR sc s₀) := Region.sub_prefix (by omega_using [hf])
  refine ⟨hk.x19, h20, h1, (hp.i_s.sub_left hv).sub_right hs, Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hB, hNL]),
    (hp.i_s.sub_left hb).sub_right hs, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ iR, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hf]⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩

/-- The compression of the block into the hash value. -/
theorem cmp_ok {t : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ t) (h20 : t.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (h1 : t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀)
    {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s' → s'.gpr .x21 = t.gpr .x21 →
      hH.md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) = hH.md.compress (hH.md.stateAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀))
        (hH.md.blockAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀)) → Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.sizes hH hp
  have z : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ + BitVec.ofNat 64 0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ := BitVec.add_zero _
  have kp : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.koregs, r ∈ preserved ∧ r ≠ .x30 := by decide
  refine compressAt_ok hH.comp (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.callOk hH hp hk h20 h1) fun s' hrd hwr hcs hsp hfr hst =>
    k s' (hk.keep hrd hwr hsp (fun r hr => hcs r (kp r hr).1 (kp r hr).2) hfr ?_)
      (hcs _ (by decide) (by decide)) hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · have := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_inR hp (a := 0) (n := H.P.N) (by omega); rwa [z] at this
  · exact (Offset.base_disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀) (k := H.P.so) (e := 8 * H.stream.W) (n := 56)
      (by show H.P.so ≤ 8 * ((H.P.so + 48) / 8); omega_using [])
      (by show 8 * ((H.P.so + 48) / 8) + 56 ≤ 2 ^ 64; omega_using [h8, hf])).symm

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s) (h21 : s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) :
    WP isa (.block H.finOut) s fun s' => ∃ t, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ t ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀))).take H.D ∧ s'.mem = t.mem ∧
      s'.sp = t.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, pR⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have hdl := hH.md.digest_length (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀))
  have k9 : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.koregs, r ≠ .x9 := by decide
  have hL : 8 * H.stream.W + 56 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 56 := rfl
    have hp_fits := hp.fits
    omega_using [hp_fits, this]
  have fin : ∀ t, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ t → bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀))).take H.D →
      WP isa (.block H.stream.restore) t fun s' => ∃ t, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ t ∧
        bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀))).take H.D ∧ s'.mem = t.mem ∧
        s'.sp = t.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → s'.gpr r = t.gpr r) :=
    fun t kt bt =>
      WP.mono (restore_ok H.stream kt.x23 (Nat.le_trans hp.hW (by decide)) kt.saved (by rw [kt.wr]; exact sR) hL)
        fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨t, kt, bt, hm, hsp, hg, ho⟩
  have x19_in : InRegions (s.rd ++ s.wr) (s.gpr .x19) H.P.N := by
    have := Offset.contains_base (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) (d := 0) (n := H.P.N) (k := H.P.N + H.P.B) (by omega_using []) (by omega)
    rw [z] at this
    rw [hk.x19, hk.rd, hk.wr]
    exact ⟨_, List.mem_append_right _ iR, this⟩
  unfold Hash.finOut
  by_cases hDN' : H.D < H.P.N
  · simp only [hDN', ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (hH.shape.out s x19_in (by
        rw [h21, hk.wr]; exact ⟨_, iR, Offset.contains_base _ (by omega_using [hS, hNL]) (by omega_using [hB, hNL])⟩)
      (by rw [hk.x19, h21]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hB, hNL])))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
    rw [h21, hk.x19] at m₁
    have f₁ : Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀, H.P.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₁ : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s₁ := hk.keep rd₁ wr₁ sp₁ (fun r hr => g₁ r (k9 r hr)) f₁
      (by simp only [List.mem_singleton]; rintro r rfl; exact VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_inR hp (by omega_using [hNL]))
    have b₁ : bytesAt s₁.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀))).take H.D := by
      rw [bytesAt_take _ _ (Nat.le_of_lt hDN'), m₁, bytesAt_writeBytes_self' hdl (by omega_using [hB, hNL])]
    have x21₁ : s₁.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ := by rw [g₁ _ (by decide), h21]
    simp only [Hash.copy32]
    refine copy32_ok (src := .x21) (dst := .x24) (by decide) (by decide) 0 0 (H.D / 4) ⟨rfl, by omega_using [hB, hpad]⟩
      ⟨rfl, by omega⟩ _ s₁ _
      (fun j hj => by
        rw [x21₁, add_ofNat, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
        exact ⟨_, List.mem_append_right _ iR, Offset.contains_base _ (by omega_using [hj, hS, hpad]) (by omega)⟩)
      (fun j hj => by
        rw [k₁.x24, add_ofNat, k₁.wr]
        exact ⟨_, pR, Offset.contains_base _ (by show 0 + 4 * j + 4 ≤ H.D; omega_using [hj]) (by omega_using [hj, hB, hpad])⟩)
      (by
        rw [x21₁, k₁.x24, eD, add_ofNat]
        exact hp.i_p.sep (Offset.contains_base _ (by omega_using [hS, hpad]) (by omega_using [hB, hNL]))
          (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega) (by omega)))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
    rw [x21₁, k₁.x24, eD, z, z] at m₂
    refine fin s₂ (k₁.keep rd₂ wr₂ sp₂ (fun r hr => g₂ r (k9 r hr))
      (m₂ ▸ VG.WriteBytes.writeBytes_frame _ _ _ (R := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H.stream) s₀) (by
        rw [bytesAt_length]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp))) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hB, hpad]), b₁]
  · have eDN : H.D = H.P.N := by omega_using [hDN', hDN]
    simp only [hDN', ↓reduceIte, List.cons_append]
    refine wp_mov fun s₁ u₁ => ?_
    rw [WP.block_append_iff]
    have x19₁ : s₁.gpr .x19 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ := by rw [u₁.other _ (by decide), hk.x19]
    refine WP.mono (hH.shape.out s₁ (by rw [u₁.rd, u₁.wr, u₁.other _ (by decide)]; exact x19_in) (by
        rw [u₁.gpr, hk.x24, u₁.wr, hk.wr, ← eDN]; exact ⟨_, pR, Region.contains_self _ _⟩)
      (by rw [x19₁, u₁.gpr, hk.x24, ← eDN]; exact hp.i_p.sub_left (Region.sub_prefix (by omega_using [hS, hpad]))))
      fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
    rw [x19₁, u₁.gpr, hk.x24, u₁.mem] at m₂
    refine fin s₂ (hk.keep (rd₂.trans u₁.rd) (wr₂.trans u₁.wr) (sp₂.trans u₁.sp) (fun r hr => by
        rw [g₂ r (k9 r hr), u₁.other r (by revert hr; revert r; decide)])
      (m₂ ▸ VG.WriteBytes.writeBytes_frame _ _ _ (R := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.opR (H := H.stream) s₀) (by
        rw [hdl, ← eDN]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp))) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (by omega_using [hB, hNL]), List.take_of_length_le (by omega_using [hdl])]

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.sizes hH hp
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pro_ok hp) (by rfl)) fun s₁ ⟨⟨k₁, di₁, dx₁, f₁⟩, hv₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (WP.preservedV (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.fin1Args_ok hH.stream hp k₁ di₁ dx₁) (by rfl))
    fun t₁ ⟨⟨kt₁, a₁, si₁, m₁⟩, hva₁⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.finCall_ok hH.stream hp kt₁ a₁ fun s₂ hv₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.mid_ok hH hp k₂) (by rw [Code.allInstrs_eq]; exact hH.finMid_keepsV))
    fun s₃ ⟨⟨k₃, x20₃, x21₃, x1₃, i₃, b₃, p₃⟩, hv₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cmp_ok hH hp k₃ x20₃ x1₃ (Q := fun s' => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s' ∧
      s'.gpr .x21 = s₃.gpr .x21 ∧ hH.md.stateAt s'.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) =
        hH.md.compress (hH.md.stateAt s₃.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀)) (hH.md.blockAt s₃.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀)))
      fun s₄ k₄ x21₄ e₄ => ⟨k₄, x21₄, e₄⟩)
    (by rw [Code.allInstrs_eq]; exact hH.cmp_keepsV)) fun s₄ ⟨⟨k₄, x21₄, e₄⟩, hv₄⟩ => ?_)
  refine WP.mono (WP.preservedV (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.out_ok hH hp k₄ (x21₄.trans x21₃))
    (by rw [Code.allInstrs_eq]; exact hH.finOut_keepsV))
    fun s' ⟨⟨s₅, k₅, m₅, hm, hsp, hg, ho⟩, hv₅⟩ => ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.abi_of k₅ hsp (fun r hr => by
      rw [hv₅ r hr, hv₄ r hr, hv₃ r hr, hv₂ r hr, hva₁ r hr, hv₁ r hr]) hg ho, ?_⟩
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.P.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until the inner digest is written.
  have oI : ∀ r ∈ [saveR H.stream (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀)], Region.Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H.stream) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp)
  have o₂ : ∀ r ∈ [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inR (H := H.stream) s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.tR (H := H.stream) s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.calR hH.stream s₀,
      VG.Proof.Pbkdf2.Md.AArch64.HmacFin.stkR s₀], Region.Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outerR (H := H.stream) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.t_sub hp)
    · exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cal_sub hH.stream hp)
    · exact hp.stk_o.symm
  have rO₂ := VG.Proof.Pbkdf2.Md.AArch64.Calls.repr_keep hH.stream f₂ o₂ (m₁ ▸ VG.Proof.Pbkdf2.Md.AArch64.Calls.repr_keep hH.stream f₁ oI hrO)
  -- The inner digest.
  have dig : (bytesAt s₂.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.T (H := H.stream) s₀) H.P.N).take H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) :=
    d₂ _ (m₁ ▸ VG.Proof.Pbkdf2.Md.AArch64.Calls.repr_keep hH.stream f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The outer hash: one compression of the outer hash value.
  have hxl : (xorPad k0 opad).length = H.P.B := by rw [xorPad_length, hk0]
  have ho : hH.md.stateAt s₃.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) = hH.md.compressList hH.iv (xorPad k0 opad) 1 := by
    rw [hH.reloc s₂.mem s₃.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.outer s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀) i₃]
    exact Md.stateAt_of_repr hB0 hxl ((hH.repr _ _ _).1 rO₂)
  show bytesAt s'.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hm, m₅, e₄, ho, hH.md.blockAt_eq (by omega_using [hpad]) p₃, b₃, hmacBlockKey, ← dig,
    ← bytesAt_take _ _ hDN, hH.iterOk.link.hash_block hxl (bytesAt_length _ _ _)]

end

/-! ## Constant time -/

section

variable {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H.stream) sc s₀) (hp' : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Pre (H := H.stream) sc s₀')
  (hq : VG.Proof.Pbkdf2.Md.AArch64.Calls.PubEq s₀ s₀')

omit hH in
/-- The registers `oregs` and the stack pointer agree in two runs. -/
theorem ko_agree (hq : VG.Proof.Pbkdf2.Md.AArch64.Calls.PubEq s₀ s₀') {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s ∧ s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀)
    (h' : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀' s' ∧ s'.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀') : s.sp = s'.sp ∧ ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.oregs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.1.sp, h'.1.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.1.x19, h'.1.x19, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn, hq.x0]
  · rw [h.2, h'.2, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn, hq.x0]
  · rw [h.1.x23, h'.1.x23, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr, hq.x4]
  · rw [h.1.x24, h'.1.x24, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.op, hq.x3]

omit hH in
theorem callOk_congr {t : State} {N B so : Nat} {a b c a' b' c' : Addr} (h : CallOk t N B so a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : CallOk t N B so a' b' c' := by
  subst ha hb hc; exact h

include hH hp hp' hq

theorem ct (hc : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.stream.finPrologue)
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀ s ∧ s.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀' s' ∧ s'.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀' ∧ s'.gpr .x2 = s₀'.gpr .x2) :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.fin_rel' hH.stream hp hp' hq (c := s₀.gpr .x2)
    (F := fun s => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀ s ∧ s.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2)
    (F' := fun s => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀' s ∧ s.gpr .x0 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀' ∧ s.gpr .x2 = s₀'.gpr .x2) hc.fin1
    (fun _ _ h h' => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.fin1Args_ok hH.stream hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.fin1Args_ok hH.stream hp' k d x) fun _ ⟨k, a, si, m⟩ =>
      ⟨k, a, si.trans hq.x2.symm, m⟩)
  have mid : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀ s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KR (H := H.stream) s₀' s') (.block H.finMid)
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s ∧ s.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ ∧ s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ ∧ s.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀' s' ∧ s'.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀' ∧ s'.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀') :=
    rel_taint VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pubRegs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.kr_agree hq h h') hc.mid
      (fun s k => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.mid_ok hH hp k) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
      (fun s k => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.mid_ok hH hp' k) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  have e₀ : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.inn s₀ := hq.x0.symm
  have e₄ : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ := hq.x4.symm
  have eb : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ := by rw [VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk, e₀]
  have cmp : RelCT isa (fun s s' =>
        (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s ∧ s.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀ ∧ s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀ ∧ s.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀' s' ∧ s'.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.scr s₀' ∧ s'.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀'))
      (compressAt H.compN H.compC)
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s ∧ s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) ∧ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀' s' ∧ s'.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀') :=
    rel_wp (compressAt_rel hH.comp fun s s' ⟨⟨k, x20, _, x1⟩, ⟨k', x20', _, x1'⟩⟩ =>
        ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacFin.callOk hH hp k x20 x1, VG.Proof.Pbkdf2.Md.AArch64.HmacFin.callOk_congr (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.callOk hH hp' k' x20' x1') e₀ e₄ eb, by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun s ⟨k, x20, x21, x1⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cmp_ok hH hp k x20 x1 fun s' k' e _ => ⟨k', e.trans x21⟩)
      (fun s ⟨k, x20, x21, x1⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.cmp_ok hH hp' k x20 x1 fun s' k' e _ => ⟨k', e.trans x21⟩)
  obtain ⟨_, hr⟩ := hc.out
  have out : RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀ s ∧ s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀) ∧ (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.KO H s₀' s' ∧ s'.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacFin.blk H s₀'))
      (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacFin.oregs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacFin.ko_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (fin1.seq (mid.seq (cmp.seq out)))

end

/-- HMAC's `finalize` is verified against `finG`, given the taint checks. -/
theorem verified {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.AArch64.HmacFin.Checks H) (hfit : H.stream.buf + H.stream.F ≤ 8 * sc)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified AArch64.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.AArch64.HmacFin.correct hH (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pre_of hH.stream sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.ct hH (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pre_of hH.stream sc h₁ hfit) (VG.Proof.Pbkdf2.Md.AArch64.HmacFin.pre_of hH.stream sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.HmacFin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.HmacInit`. -/
section

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `init`

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacInit.lean`): HMAC's `init`
(`Impl/Pbkdf2/Md/AArch64.lean`) saves our caller's registers and our return
address (`pro_ok`), sets each state's hash value with the streaming `init`
(`callInit_ok`), writes `K₀ ⊕ ipad` into the inner state's buffer and
`K₀ ⊕ opad` into the outer one's (`keys_ok`), compresses each buffer into
its state's hash value (`cmp_ok`), and loads our caller's registers back.
A state whose initial hash value has absorbed the block in its buffer
represents that block (`Md.repr_block`). No instruction of `init` or of
the functions it calls writes a SIMD register (`HashOK.hmacInit_keepsV`), so
it keeps their low halves. Constant time: the taint analysis checks the
pieces between the calls (`Checks`); the calls are constant time by the
callees' own proofs.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacInit

open VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream.AArch64 (add_ofNat Upd Mupd wp_mov wp_movz wp_addImm wp_add wp_sub wp_ldrb wp_strb
  wp_ldr32 wp_str32 eval_zero ofNat_succ toNat_ofNat_lt)
open VG.Impl.MdStream.AArch64 (compressAt mov)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (CallOk compressAt_ok compressAt_rel)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG rel_taint rel_wp init_call init_rel SavedRegs saveR save_ok
  restore_ok savedRegs count_loop wp_eor movz_ofNat sub_ofNat' ofNat_ne_zero repr_keep PubEq args untouched)
open VG.Proof.Hmac.Generic.Common (K0 K0_length covers_one InRegions.right' bytes_keep bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_sep)
open VG.Proof.Pbkdf2.MdKeys (ipadBlk ipadBlk_length ipadBlk_zero ipadBlk_succ ipadBlk_eq writeBytes_set fill_mem
  xorOpad_mem xorOpad_ipad xor_byte)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## Constants -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem movzk_val (lo hi : BitVec 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 lo))) &&&
        BitVec.setWidth 64 (~~~((65535 : BitVec 32) <<< 16)) |||
      BitVec.setWidth 64 (BitVec.setWidth 32 hi <<< 16) = BitVec.setWidth 64 (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h1 : i < 16
  · simp [h1, show i < 32 by omega, hi']
  · by_cases h2 : i < 32
    · simp [h1, h2, hi']
      rw [BitVec.getLsbD_of_ge lo i (by omega)]
      simp [show i - 16 < 32 by omega]
    · simp [h1, h2, hi']
      exact BitVec.getLsbD_of_ge hi (i - 16) (by omega)

/-- `movz wd, #lo; movk wd, #hi, lsl #16`: the word `hi ++ lo`. -/
theorem wp_movzk {d : Reg} {lo hi : BitVec 16}
    (k : ∀ s', Upd s s' d ((hi ++ lo).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .w d lo 0 :: .movk .w d hi 1 :: is)) s Q := by
  refine Proof.MdStream.AArch64.WP.cons (s' := s.write .w d (lo.setWidth 32)) (by simp [exec]) ?_
  refine Proof.MdStream.AArch64.WP.cons (s' := (s.write .w d (lo.setWidth 32)).write .w d (hi ++ lo)) ?_
    (k _ ?_)
  · simp only [exec, State.read, State.write, Size.bits]
    simp only [show 16 * 1 < 32 by decide, ↓reduceIte, Option.some.injEq]
    congr 1
    funext r'
    by_cases h : r' = d
    · simp only [h, ↓reduceIte]; exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.movzk_val lo hi
    · simp [h]
  · exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

end

/-- `ipad` in every byte of a word. -/
abbrev c36 : BitVec 64 := ((0x3636 : BitVec 16) ++ (0x3636 : BitVec 16)).setWidth 64

/-- `ipad ⊕ opad` in every byte of a word. -/
abbrev c6a : BitVec 64 := ((0x6a6a : BitVec 16) ++ (0x6a6a : BitVec 16)).setWidth 64

theorem c36_32 : c36.setWidth 32 = (0x36363636 : BitVec 32) := by decide

theorem c36_8 : c36.setWidth 8 = ipad := by decide

theorem c6a_32 : c6a.setWidth 32 = (0x6a6a6a6a : BitVec 32) := by decide

theorem xor_word (x : BitVec 32) (c : BitVec 64) : (x.setWidth 64 ^^^ c).setWidth 32 = x ^^^ c.setWidth 32 := by
  ext i hi; simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev kp : Addr := s₀.gpr .x2
abbrev kl : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀, H.S⟩
abbrev outR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀, H.S⟩
abbrev keyR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀⟩
abbrev stkR : Region := below s₀.sp 16
/-- The compression function's working space. -/
abbrev calR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀, H.P.so⟩
/-- Where our caller's registers are saved. -/
abbrev svR : Region := saveR H.stream (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀)
/-- The buffer of the state at `p`. -/
abbrev bufOf (p : Addr) : Addr := p + BitVec.ofNat 64 H.P.N
/-- The key, padded to a block. -/
abbrev k0 : List Byte := VG.Proof.Hmac.Generic.Common.K0 s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀) H.P.B

end

abbrev scR (sc : Nat) (s₀ : State) : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀, 8 * sc⟩

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀ ≤ H.P.B
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀)
  i_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀)
  o_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀)
  k_i : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀)
  k_o : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀)
  k_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀)
  stk_o : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀)
  stk_k : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀)
  stk_s : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀)
  nw : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.stream.buf ≤ 8 * sc

variable {H : Hash} (hH : HashOK H)

theorem pre_of {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.stream.buf ≤ 8 * sc) :
    VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hfit⟩

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.P.N ≤ 64 ∧ 0 < H.P.B ∧ H.P.B ≤ 128 ∧
    H.P.so + 48 = 8 * H.stream.W ∧ H.stream.buf = 8 * H.stream.W + 56 ∧ H.stream.W ≤ 134 ∧
    8 * H.stream.W + 56 ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 := by
  have := hH.sizes.N4; have := hH.N_le; have := hH.B_le; have := hH.B_pos; have := hH.sizes.dims.so
  have := hp.nw; have := hp.fits
  have hb : H.stream.buf = 8 * H.stream.W + 56 := rfl
  have hw : H.stream.W = (H.P.so + 48) / 8 := rfl
  have hmd : H.P.md.so = H.P.so := rfl
  have : H.P.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega
  omega

/-! ## The parts of the regions -/

theorem save_sub : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.svR H s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  exact Offset.sub_base _ h

theorem cal_sub : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.calR H s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  exact Region.sub_prefix (by omega)

theorem cal_save : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.calR H s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.svR H s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', h''⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  have := hp.nw
  exact Offset.base_disjoint _ (by omega) (by omega)

/-- What a state's region is: writable, and apart from the others. -/
structure StOk (p : Addr) : Prop where
  mem : ⟨p, H.S⟩ ∈ s₀.wr
  sc : Region.Disjoint ⟨p, H.S⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀)
  stk : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀).Disjoint ⟨p, H.S⟩
  key : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀).Disjoint ⟨p, H.S⟩

omit hH in
theorem stOk_in : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) :=
  ⟨by rw [hp.wr]; simp, hp.i_s, hp.stk_i, hp.k_i⟩

omit hH in
theorem stOk_out : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) :=
  ⟨by rw [hp.wr]; simp, hp.o_s, hp.stk_o, hp.k_o⟩

/-- A region the code may write while our caller's registers and the key
stay put. -/
structure Away (r : Region) : Prop where
  sv : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.svR H s₀).Disjoint r
  key : (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀).Disjoint r

theorem away_st {p : Addr} (hs : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {r : Region}
    (h : Region.Sub r ⟨p, H.S⟩) : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Away (H := H) (s₀ := s₀) r :=
  ⟨(hs.sc.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.save_sub hH hp)).sub_right h, hs.key.sub_right h⟩

theorem away_cal : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Away (H := H) (s₀ := s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.calR H s₀) :=
  ⟨(VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cal_save hH hp).symm, hp.k_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cal_sub hH hp)⟩

theorem away_stk {r : Region} (h : Region.Sub r (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀)) : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Away (H := H) (s₀ := s₀) r :=
  ⟨(hp.stk_s.symm.sub_left (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.save_sub hH hp)).sub_right h, hp.stk_k.symm.sub_right h⟩

end

/-! ## What holds from the prologue on -/

/-- The registers and memory kept from the prologue on, with `x19 = b` (the
state being compressed). -/
structure KR (H : Hash) (s₀ : State) (b : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = b
  x20 : s.gpr .x20 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀
  x21 : s.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀
  x22 : s.gpr .x22 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀
  x23 : s.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀
  x24 : s.gpr .x24 = s₀.gpr .x3
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.stream (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀) s₀ s.mem
  key : ∀ i < VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀, s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀ + BitVec.ofNat 64 i)

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- Those the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

theorem kregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem KR.keep {s₀ s s' : State} {b : Addr} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (ha : ∀ r ∈ rs, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Away (H := H) (s₀ := s₀) r) : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19, (hg _ (by simp)).trans h.x20,
    (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x22, (hg _ (by simp)).trans h.x23,
    (hg _ (by simp)).trans h.x24, fun r hr => (hg r (by revert r; decide)).trans (h.cs r hr),
    h.saved.frame H.stream hf fun r hr => (ha r hr).sv,
    fun i hi => (hf.bytes (R := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀) (fun r hr => (ha r hr).key) (Nat.le_of_lt (s₀.gpr .x3).isLt)
      hi).trans (h.key i hi)⟩

theorem KR.regs {s₀ s s' : State} {b : Addr} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s' :=
  h.keep (rs := []) hrd hwr hsp hg (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem KR.upd {s₀ s s' : State} {b : Addr} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs) {v : BitVec 64}
    (u : Upd s s' d v) : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s' :=
  h.regs u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-! ## The prologue -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc s₀)
include hH hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hL, -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  unfold Hash.initPrologue
  refine save_ok H.stream (scr := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀) rfl (by omega) (by rw [hp.wr]; simp) hL
    fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_mov fun s₇ u₇ => WP.block_nil ?_
  have hm : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other r hr.2.2.2.2.2, u₆.other r hr.2.2.2.2.1, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1,
      u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have hk : ∀ r ∈ [VG.Proof.Pbkdf2.Md.AArch64.HmacInit.svR H s₀], (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.k_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.save_sub hH hp)
  exact ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, g₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, g₁],
    by simp (disch := decide) only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, g₁],
    by simp (disch := decide) only [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁],
    fun r hr => g r (by revert r; decide),
    hm ▸ sv₁,
    fun i hi => by
      rw [hm]; exact f₁.bytes (R := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keyR s₀) hk (Nat.le_of_lt (s₀.gpr .x3).isLt) hi⟩

/-! ## The calls of the streaming `init` -/

/-- A call of the streaming `init` on the state at `p`, from the register `st`. -/
theorem callInit_ok {b : Addr} {s : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hst : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s' → Frame [⟨p, H.S⟩, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.stream.callInit st) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s₁ := hk.upd (by decide) u₁
  refine init_call hH.stream (st := p) (by rw [u₁.gpr, hs]) (by rw [k₁.wr]; exact covers_one hst.mem)
    fun s' ha hr => ?_
  have f := ha.frame
  rw [k₁.sp, u₁.mem] at f
  refine hQ s' (k₁.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs_pres r hr).2)
      (u₁.mem ▸ f) ?_) f hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_st hH hp hst (fun _ h => h)
  · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_stk hH hp (fun _ h => h)

end

/-! ## The padded keys -/

/-- Stores of `ipad` words (the low half of `x14`) at `x19 + o + 4 k`, for
`k < n`, which write `4 n` bytes of `ipad` from `p = x19 + o`. -/
theorem fill_ok {o : Nat} {p : Addr} (ho : o % 4 = 0) : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    o + 4 * n ≤ 4096 * 4 → s.gpr .x19 + BitVec.ofNat 64 o = p → s.gpr .x14 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.c36 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (4 * k)) 4) → 4 * n + 4 < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem p (List.replicate (4 * n) ipad) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .w .x14 .x19 (o + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hb hp hax hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q (by omega) hp hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str32 (a := p + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁, ← hp, add_ofNat]) (by rw [wr₁]; exact hout n (by omega)) fun s₂ m₂ =>
        k s₂ (by rw [m₂.gpr, g₁]) (by rw [m₂.rd, rd₁]) (by rw [m₂.wr, wr₁]) (by rw [m₂.sp, sp₁]) ?_
    rw [m₂.mem, g₁, hax, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.c36_32, m₁, fill_mem _ _ _ (by omega), Nat.mul_succ]

/-- After `j` bytes of the key at `K` (whose bytes are those of `mk`), from the
state `s` the loop starts in: the buffer at `P` holds `ipadBlk … j` over `m`. -/
structure KeyInv (s : State) (m mk : Mem) (P K : Addr) (B j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ [Reg.x9, .x10, .x11, .x12, .x13], t.gpr r = s.gpr r
  x10 : t.gpr .x10 = BitVec.ofNat 64 j
  mem : t.mem = VG.WriteBytes.writeBytes m P (ipadBlk mk K B j)

/-- Where the key loop reads and writes. -/
structure KeyRegs (H : Hash) (s : State) (m mk : Mem) (P K : Addr) (kl : Nat) : Prop where
  kl_le : kl ≤ H.P.B
  hB : H.P.B ≤ 128
  hN : H.P.N ≤ 64
  x22 : s.gpr .x22 = K
  x19 : s.gpr .x19 + BitVec.ofNat 64 H.P.N = P
  x24 : s.gpr .x24 = BitVec.ofNat 64 kl
  x14 : s.gpr .x14 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.c36
  key : ∀ i < kl, m (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i)
  kin : ∀ i < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1
  bout : ∀ i < H.P.B, InRegions s.wr (P + BitVec.ofNat 64 i) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, H.P.B⟩

theorem key_step {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyRegs H s m mk P K kl) {j : Nat}
    (hj : j < kl) {t : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyInv s m mk P K H.P.B j t) :
    WP isa (.block [.add .x .x13 .x22 .x10, .ldrb .x9 .x13 0, .logic .eor .x .x9 .x9 .x14,
      .add .x .x12 .x19 .x10, .strb .x9 .x12 H.P.N, .addImm .x .x10 .x10 1, .sub .x .x11 .x24 .x10]) t
      fun t' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyInv s m mk P K H.P.B (j + 1) t' ∧ t'.gpr .x11 = BitVec.ofNat 64 (kl - (j + 1)) := by
  have hkl := hr.kl_le
  have hB := hr.hB
  have hN := hr.hN
  have hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = mk (K + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hr.key j hj]
    refine (VG.WriteBytes.writeBytes_frame m P _ (R := ⟨P, H.P.B⟩) (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨K, kl⟩) ?_ (by show kl ≤ 2 ^ 64; omega) hj
    simp only [List.mem_singleton]; rintro r rfl; exact hr.disj
  have o : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13] → t.gpr r = s.gpr r := h.other
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.gpr, o _ (by decide), hr.x22, h.x10, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hr.kin j hj) fun t₂ u₂ => ?_
  refine wp_eor fun t₃ u₃ => wp_add fun t₄ u₄ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega)
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), o _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x10, ← hr.x19]; ac_rfl)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hr.bout j (by omega)) fun t₅ m₅ => ?_
  refine wp_addImm (by decide) fun t₆ u₆ => wp_sub fun t₇ u₇ => WP.block_nil ?_
  have h10 : t₆.gpr .x10 = BitVec.ofNat 64 (j + 1) := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.x10]
    exact (ofNat_succ j).symm
  refine ⟨⟨by rw [u₇.rd, u₆.rd, m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₇.sp, u₆.sp, m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [u₇.other r hr'.2.2.1, u₆.other r hr'.2.1, m₅.gpr, u₄.other r hr'.2.2.2.1, u₃.other r hr'.1,
        u₂.other r hr'.1, u₁.other r hr'.2.2.2.2, h.other r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1,
          hr'.2.2.2.2])],
    by rw [u₇.other _ (by decide), h10], ?_⟩, ?_⟩
  · have v : (t₄.gpr .x9).setWidth 8 = mk (K + BitVec.ofNat 64 j) ^^^ ipad := by
      rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        o _ (by decide), hr.x14, xor_byte, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.c36_8, u₁.mem, hbyte]
    rw [u₇.mem, u₆.mem, m₅.mem, v, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem,
      writeBytes_set _ _ _ (by rw [hl]; omega) (by rw [hl]; omega), ipadBlk_succ]
  · rw [u₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), o _ (by decide), hr.x24, h10,
      sub_ofNat' (by omega) (by omega)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyRegs H s m mk P K kl)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 0) (hm : s.mem = VG.WriteBytes.writeBytes m P (ipadBlk mk K H.P.B 0)) :
    WP isa (.ite (.zero .x .x24) (.block []) H.keyLoop) s (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyInv s m mk P K H.P.B kl) := by
  have i0 : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyInv s m mk P K H.P.B 0 s := ⟨rfl, rfl, rfl, fun _ _ => rfl, h10, hm⟩
  have hkl := hr.kl_le
  have hB := hr.hB
  have hz : isa.eval (.zero .x .x24) s = some (decide (kl = 0)) := by
    show VG.AArch64.eval (.zero .x .x24) s = _
    rw [eval_zero, hr.x24]
    congr 1
    by_cases hk : kl = 0
    · simp [hk]
    · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hk this
  refine WP.ite (decide (kl = 0)) hz (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (by omega) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyInv s m mk P K H.P.B) (fun j hj t h => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.key_step hr hj h) i0

/-- The words of the outer buffer: `n` words of the inner buffer at
`x19 + N`, XORed with `ipad ⊕ opad` (`x15`), to `x21 + N`. -/
theorem opad_ok (hN : H.P.N % 4 = 0) : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    H.P.N + 4 * n ≤ 4096 * 4 → s.gpr .x15 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.c6a →
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr .x19 + BitVec.ofNat 64 H.P.N) (4 * n) (s.gpr .x21 + BitVec.ofNat 64 H.P.N) (4 * n) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x21 + BitVec.ofNat 64 H.P.N)
        ((bytesAt s.mem (s.gpr .x19 + BitVec.ofNat 64 H.P.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [bytesAt, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro rest s Q hb h15 hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (by omega) h15 (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_ldr32 (a := s.gpr .x19 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ (by decide), add_ofNat]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_eor fun s₃ u₃ => ?_
    refine wp_str32 (a := s.gpr .x21 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), add_ofNat])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ m₄ => k s₄ (fun r hr => by rw [m₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [m₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [m₄.wr, u₃.wr, u₂.wr, wr₁]) (by rw [m₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    rw [m₄.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), g₁ _ (by decide), h15, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.xor_word, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.c6a_32, u₃.mem,
      u₂.mem, m₁, Nat.mul_succ, xorOpad_mem _ _ _ _ (by rwa [← Nat.mul_succ]) (by omega)]

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc s₀)
include hH hp

/-- `K₀ ⊕ ipad` into the inner buffer and `K₀ ⊕ opad` into the outer one, and
the inner block's address in `x1`. -/
theorem keys_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s) :
    WP isa H.initKeys s fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) t ∧ t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) ∧
      Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀), H.P.B⟩, ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀), H.P.B⟩] s.mem t.mem ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) ipad ∧
      bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) opad := by
  obtain ⟨hN4, hB4, hN, hB0, hB, -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  have hkl := hp.kl_le
  have eB : 4 * (H.P.B / 4) = H.P.B := by omega
  have si := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_in (H := H) hp
  have so := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_out (H := H) hp
  have hS : H.S = H.P.N + H.P.B := rfl
  have bI : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀), H.P.B⟩ ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀), H.P.B⟩ ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have inI : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, si.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have inO : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, so.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dIO : Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀), H.P.B⟩ ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀), H.P.B⟩ :=
    (hp.i_o.sub_left bI).sub_right bO
  unfold Hash.initKeys Hash.ipadFill
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.wp_movzk fun s₁ u₁ => ?_)
  refine VG.Proof.Pbkdf2.Md.AArch64.HmacInit.fill_ok (o := H.P.N) (p := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) (by omega) (H.P.B / 4) _ s₁ _ (by omega)
    (by rw [u₁.other _ (by decide), hk.x19]) u₁.gpr (fun k hk' => by rw [u₁.wr, hk.wr]; exact inI _ 4 (by omega))
    (by omega) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_movz fun s₃ u₃ => WP.block_nil ?_
  have G₃ : ∀ r, r ≠ .x14 → r ≠ .x10 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h2, g₂, u₁.other r h1]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd, hk.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr, hk.wr]
  have hr : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KeyRegs H s₃ s.mem s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀) :=
    { kl_le := hkl, hB := hB, hN := hN
      x22 := by rw [G₃ _ (by decide) (by decide), hk.x22]
      x19 := by rw [G₃ _ (by decide) (by decide), hk.x19]
      x24 := by rw [G₃ _ (by decide) (by decide), hk.x24, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      x14 := by rw [u₃.other _ (by decide), g₂, u₁.gpr]
      key := hk.key
      kin := fun i hi => by
        rw [rd₃, wr₃, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          Offset.contains_base _ (by omega) (by omega)⟩
      bout := fun i hi => by rw [wr₃]; exact inI i 1 (by omega)
      disj := hp.k_i.sub_right bI }
  have h10 : s₃.gpr .x10 = BitVec.ofNat 64 0 := by rw [u₃.gpr]; rfl
  have hm : s₃.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) (ipadBlk s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀) H.P.B 0) := by
    rw [u₃.mem, m₂, u₁.mem, ipadBlk_zero, eB]
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.key_ok hr h10 hm) fun t ht => ?_)
  have Gt : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14] → t.gpr r = s.gpr r := fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ht.other r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1]),
      G₃ r hr'.2.2.2.2.2 hr'.2.1]
  have bxt : t.gpr .x19 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀ := by rw [Gt _ (by decide), hk.x19]
  have x21t : t.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀ := by rw [Gt _ (by decide), hk.x21]
  have rdt : t.rd = s₀.rd := by rw [ht.rd, rd₃]
  have wrt : t.wr = s₀.wr := by rw [ht.wr, wr₃]
  unfold Hash.opadFill
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Pbkdf2.Md.AArch64.HmacInit.wp_movzk fun t₁ v₁ => ?_
  have bxt₁ : t₁.gpr .x19 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀ := by rw [v₁.other _ (by decide), bxt]
  have x21t₁ : t₁.gpr .x21 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀ := by rw [v₁.other _ (by decide), x21t]
  refine VG.Proof.Pbkdf2.Md.AArch64.HmacInit.opad_ok hN4 (H.P.B / 4) _ t₁ _ (by omega) v₁.gpr
    (fun k hk' => by rw [bxt₁, v₁.rd, v₁.wr, rdt, wrt]; exact InRegions.right' (inI _ 4 (by omega)))
    (fun k hk' => by rw [x21t₁, v₁.wr, wrt]; exact inO _ 4 (by omega))
    (by rw [bxt₁, x21t₁, eB]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  refine wp_addImm (by omega) fun s₆ u₆ => WP.block_nil ?_
  rw [bxt₁, x21t₁, eB, v₁.mem] at m₅
  have G : ∀ r, r ∉ [Reg.x1, .x9, .x10, .x11, .x12, .x13, .x14, .x15] → s₆.gpr r = s.gpr r := fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [u₆.other r hr'.1, g₅ r hr'.2.1, v₁.other r hr'.2.2.2.2.2.2.2,
      Gt r (by simp [hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1, hr'.2.2.2.2.2.1, hr'.2.2.2.2.2.2.1])]
  have hm₆ : s₆.mem = s₅.mem := u₆.mem
  have lI : (ipadBlk s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀) H.P.B (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀)).length = H.P.B := ipadBlk_length _ _ _ _
  have bt : bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) ipad := by
    rw [ht.mem, bytesAt_writeBytes_self' lI (by omega), ipadBlk_eq _ _ hkl]
  have lO : ((bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length = H.P.B := by
    simp [bytesAt]
  have fT : Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀), H.P.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [lI]; exact Region.contains_self _ _)
  have f₅ : Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀), H.P.B⟩] t.mem s₅.mem := by
    rw [m₅]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [lO]; exact Region.contains_self _ _)
  have f : Frame [⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀), H.P.B⟩, ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀), H.P.B⟩] s.mem s₆.mem := by
    rw [hm₆]; exact (fT.mono (by simp)).trans (f₅.mono (by simp))
  refine ⟨hk.keep (by rw [u₆.rd, rd₅, v₁.rd, ht.rd, rd₃, ← hk.rd])
      (by rw [u₆.wr, wr₅, v₁.wr, ht.wr, wr₃, ← hk.wr]) (by rw [u₆.sp, sp₅, v₁.sp, ht.sp, u₃.sp, sp₂, u₁.sp])
      (fun r hr' => G r (by revert hr'; revert r; decide)) f
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_st hH hp si bI
        · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_st hH hp so bO),
    by rw [u₆.gpr, g₅ _ (by decide), bxt₁], f, ?_, ?_⟩
  · have sIO : Mem.Sep (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) H.P.B (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀))
        ((bytesAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length := by
      rw [lO]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [hm₆, m₅, bytesAt_writeBytes_sep _ _ sIO (by omega), bt]
  · rw [hm₆, m₅, bytesAt_writeBytes_self' lO (by omega), bt, xorOpad_ipad]

/-! ## The compressions -/

/-- What the call of the compression function needs, for the state at `p`. -/
theorem callOk {p : Addr} (hs : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ p t)
    (hx1 : t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p) : CallOk t H.P.N H.P.B H.P.so p (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p) := by
  obtain ⟨-, -, hN, -, hB, hso, -, -, hL, h8⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  have sR : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hv : Region.Sub ⟨p, H.P.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hb : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p, H.P.B⟩ ⟨p, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hc : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr s₀, H.P.so⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀) := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cal_sub hH hp
  refine ⟨hk.x19, hk.x20, hx1, (hs.sc.sub_left hv).sub_right hc,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hs.sc.sub_left hb).sub_right hc, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hs.mem, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ hs.mem, 0, (BitVec.add_zero _).symm,
        by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hs.mem, 0, (BitVec.add_zero _).symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩

/-- The compression of the block in the buffer of the state at `p` into its
hash value. -/
theorem cmp_ok {p : Addr} (hs : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ p t)
    (hx1 : t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p) {Q : State → Prop}
    (k : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ p s' → Frame [⟨p, H.P.N⟩, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.calR H s₀] t.mem s'.mem →
      hH.md.stateAt s'.mem p = hH.md.compress (hH.md.stateAt t.mem p) (hH.md.blockAt t.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p)) →
      Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  refine compressAt_ok hH.comp (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callOk hH hp hs hk hx1) fun s' hrd hwr hcs hsp hfr hst =>
    k s' (hk.keep hrd hwr hsp (fun r hr => hcs r (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs_pres r hr).2) hfr ?_) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_st hH hp hs (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega))
  · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_cal hH hp

/-- From the inner state to the outer one. -/
theorem mid_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s) :
    WP isa (.block H.initOuter) s fun t => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) t ∧ t.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) ∧
      t.mem = s.mem := by
  obtain ⟨-, -, hN, -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  unfold Hash.initOuter
  refine wp_mov fun s₁ u₁ => wp_addImm (by omega) fun s₂ u₂ => WP.block_nil ?_
  have G : ∀ r, r ≠ .x19 → r ≠ .x1 → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₂.other r h2, u₁.other r h1]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨by rw [u₂.rd, u₁.rd, hk.rd], by rw [u₂.wr, u₁.wr, hk.wr], by rw [u₂.sp, u₁.sp, hk.sp],
    by rw [u₂.other _ (by decide), u₁.gpr, hk.x21],
    by rw [G _ (by decide) (by decide), hk.x20], by rw [G _ (by decide) (by decide), hk.x21],
    by rw [G _ (by decide) (by decide), hk.x22], by rw [G _ (by decide) (by decide), hk.x23],
    by rw [G _ (by decide) (by decide), hk.x24],
    fun r hr => by rw [G r (by revert hr; revert r; decide) (by revert hr; revert r; decide), hk.cs r hr],
    by rw [hm]; exact hk.saved, fun i hi => by rw [hm]; exact hk.key i hi⟩,
    by rw [u₂.gpr, u₁.other _ (by decide), hk.x21], hm⟩

/-! ## Correctness -/

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp s₀) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀)) = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀ := by
  have := hp.kl_le
  simp only [blockKey, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0, VG.Proof.Hmac.Generic.Common.K0, bytesAt_length, hH.hB, show ¬ (H.P.B < VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kl s₀) by omega, ↓reduceIte]

theorem correct : WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  obtain ⟨-, -, hN, hB0, hB, -, -, hW, hL, -⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.sizes hH hp
  have hkl := hp.kl_le
  have si := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_in (H := H) hp
  have so := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_out (H := H) hp
  have hsc : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.withPreservedV ?_ hH.hmacInit_keepsV
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pro_ok hH hp) fun s₁ k₁ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callInit_ok hH hp k₁ (st := .x19) k₁.x19 si fun s₂ k₂ f₂ r₂ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callInit_ok hH hp k₂ (st := .x21) k₂.x21 so fun s₃ k₃ f₃ r₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keys_ok hH hp k₃) fun s₄ ⟨k₄, si₄, f₄, bI₄, bO₄⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cmp_ok hH hp si k₄ si₄ fun s₅ k₅ f₅ e₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.mid_ok hH hp k₅) fun s₆ ⟨k₆, si₆, m₆⟩ => ?_)
  refine WP.seq (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cmp_ok hH hp so k₆ si₆ fun s₇ k₇ f₇ e₇ => ?_)
  refine WP.mono (restore_ok H.stream k₇.x23 (by omega) k₇.saved (by rw [k₇.wr]; exact hsc) hL)
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hsp, k₇.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hg _ (by decide)
      | exact (ho _ (by decide)).trans (k₇.cs _ (by decide))
  -- What each piece keeps: the hash values and the buffers it does not write.
  have keepS : ∀ {rs : List Region} {m m' : Mem} {p : Addr}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) → hH.md.stateAt m' p = hH.md.stateAt m p :=
    fun hf hd => hH.md.stateAt_congr fun i hi =>
      hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega) hi
  have hvI : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀, H.P.N⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hvO : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀, H.P.N⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have bI : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀), H.P.B⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀), H.P.B⟩ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have nb : ∀ p : Addr, Region.Disjoint ⟨p, H.P.N⟩ ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p, H.P.B⟩ := fun p =>
    Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  have iv : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := ((hH.repr _ _ _).1 h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  -- The inner state.
  have iv₄ : hH.md.stateAt s₄.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact nb _
        · exact (hp.i_o.sub_left hvI).sub_right bO),
      keepS f₃ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.i_o.sub_left hvI
        · exact hp.stk_i.symm.sub_left hvI), iv r₂]
  have hl : (xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) ipad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rI₅ := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl bI₄ (e₅.trans (congrArg (hH.md.compress · _) iv₄))
  -- The outer state.
  have iv₆ : hH.md.stateAt s₆.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) = hH.iv := by
    rw [m₆, keepS f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right hvI
        · exact (so.sc.sub_left hvO).sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cal_sub hH hp)),
      keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right bI
        · exact nb _), iv r₃]
  have bO₆ : bytesAt s₆.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀)) H.P.B = xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) opad := by
    rw [m₆, bytes_keep f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left bO).sub_right hvI
        · exact (so.sc.sub_left bO).sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cal_sub hH hp)) (by omega), bO₄]
  have hl' : (xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) opad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rO₇ := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl' bO₆ (e₇.trans (congrArg (hH.md.compress · _) iv₆))
  -- The inner state, kept by the outer compression.
  have rI₇ : hH.SH.Repr s₇.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) (xorPad (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.k0 H s₀) ipad) :=
    VG.Proof.Pbkdf2.Md.AArch64.Calls.repr_keep hH.stream f₇ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_right hvO
      · exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cal_sub hH hp)) (m₆ ▸ (hH.repr _ _ _).2 rI₅)
  show hH.SH.Repr s'.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) _ ∧ hH.SH.Repr s'.mem (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) _
  rw [hm, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.blockKey_eq hH hp]
  exact ⟨rI₇, (hH.repr _ _ _).2 rO₇⟩

end

/-! ## Constant time -/

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.initPrologue) hc).isSome = true
  argI : ∀ st ∈ [Reg.x19, .x21], ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs) (.block [mov .x0 st])
    hc).isSome = true
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs) H.initKeys hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs) (.block H.initOuter) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs) (.block H.stream.restore) hc).isSome = true

section
variable {sc : Nat} {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc s₀) (hp' : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc s₀') (hq : VG.Proof.Pbkdf2.Md.AArch64.Calls.PubEq s₀ s₀')

omit hH in
theorem kr_agree (hq : VG.Proof.Pbkdf2.Md.AArch64.Calls.PubEq s₀ s₀') {b : Addr} {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s) (h' : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b s') :
    s.sp = s'.sp ∧ ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19]
  · rw [h.x20, h'.x20, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr, hq.x4]
  · rw [h.x21, h'.x21, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out, hq.x1]
  · rw [h.x22, h'.x22, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kp, hq.x2]
  · rw [h.x23, h'.x23, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.scr, hq.x4]
  · rw [h.x24, h'.x24, hq.x3]

omit hH in
theorem callOk_congr {t : State} {N B so : Nat} {a b c a' b' c' : Addr} (h : CallOk t N B so a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : CallOk t N B so a' b' c' := by
  subst ha hb hc; exact h

include hH hp hp' hq

/-- A call of the streaming `init` on the state at `p`, from `st`. -/
theorem callInit_rel (hc : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Checks H) {b : Addr} {st : Reg} (hst : st ∈ [Reg.x19, .x21]) {p : Addr}
    (hs : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p) (hs' : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') p)
    (hr : ∀ {t : State}, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b t → t.gpr st = p) (hr' : ∀ {t : State}, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b t → t.gpr st = p) :
    RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b s') (H.stream.callInit st)
      fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b s' := by
  have ha : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b s') (.block [mov .x0 st])
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s ∧ s.gpr .x0 = p) ∧ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b s' ∧ s'.gpr .x0 = p) :=
    rel_taint VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kr_agree hq h h') (hc.argI st hst)
      (fun _ h => wp_mov fun t u => WP.block_nil ⟨h.upd (by decide) u, by rw [u.gpr, hr h]⟩)
      (fun _ h => wp_mov fun t u => WP.block_nil ⟨h.upd (by decide) u, by rw [u.gpr, hr' h]⟩)
  have call : ∀ {t₀ : State}, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Pre H sc t₀ → VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := t₀) p → ∀ t, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H t₀ b t →
      t.gpr .x0 = p → WP isa (.call H.stream.initN H.stream.initC) t (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H t₀ b) := fun hpt hst t k d => by
    refine init_call hH.stream (st := p) d (by rw [k.wr]; exact covers_one hst.mem) fun s' ha _ => ?_
    have f := ha.frame
    rw [k.sp] at f
    refine k.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kregs_pres r hr).2) f ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_st hH hpt hst (fun _ h => h)
    · exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.away_stk hH hpt (fun _ h => h)
  refine ha.seq (rel_wp (F := fun s => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ b s ∧ s.gpr .x0 = p)
    (F' := fun s => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' b s ∧ s.gpr .x0 = p) (init_rel hH.stream (st := p) fun s s' h => ?_)
    (fun t ⟨k, d⟩ => call hp hs t k d) (fun t ⟨k, d⟩ => call hp' hs' t k d))
  obtain ⟨⟨k, d⟩, ⟨k', d'⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one hs.mem, by rw [k'.wr]; exact covers_one hs'.mem,
    by rw [k.sp, k'.sp, hq.sp]⟩

/-- A compression of the state at `p`. -/
theorem cmp_rel {p : Addr} (hs : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀) p)
    (hs' : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') p) :
    RelCT isa (fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ p s ∧ s.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p) ∧ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' p s' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H p))
      (compressAt H.compN H.compC) fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ p s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' p s' :=
  rel_wp (compressAt_rel hH.comp fun s s' ⟨⟨k, x1⟩, ⟨k', x1'⟩⟩ =>
      ⟨VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callOk hH hp hs k x1, VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callOk_congr (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callOk hH hp' hs' k' x1') rfl hq.x4.symm rfl,
        by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun s ⟨k, x1⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cmp_ok hH hp hs k x1 fun s' k' _ _ => k')
    (fun s ⟨k, x1⟩ => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cmp_ok hH hp' hs' k x1 fun s' k' _ _ => k')

theorem ct (hc : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have ei : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀ := hq.x0.symm
  have eo : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀' = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀ := hq.x1.symm
  have si := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_in (H := H) hp
  have so := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_out (H := H) hp
  have si' : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) := ei ▸ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_in (H := H) hp'
  have so' : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.StOk (H := H) (sc := sc) (s₀ := s₀') (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) := eo ▸ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.stOk_out (H := H) hp'
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s' :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pro_ok hH hp)
      (fun _ e => by rw [e, ← ei]; exact VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pro_ok hH hp')
  have c₁ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callInit_rel hH hp hp' hq hc (b := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) (st := .x19) (by simp) si si'
    (fun k => k.x19) (fun k => k.x19)
  have c₂ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.callInit_rel hH hp hp' hq hc (b := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) (st := .x21) (by simp) so so'
    (fun k => k.x21) (fun k => by rw [k.x21, eo])
  have keys : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s') H.initKeys
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s ∧ s.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀)) :=
    rel_taint VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kr_agree hq h h') hc.keys
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keys_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.keys_ok hH hp' (ei ▸ h)) fun _ h => ⟨ei ▸ h.1, by rw [h.2.1, ei]⟩)
  have mid : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.inn s₀) s') (.block H.initOuter)
      fun s s' => (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) s ∧ s.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀)) ∧
        (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) s' ∧ s'.gpr .x1 = VG.Proof.Pbkdf2.Md.AArch64.HmacInit.bufOf H (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀)) :=
    rel_taint VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs (fun _ _ h h' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kr_agree hq h h') hc.mid
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.mid_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.mid_ok hH hp' (ei ▸ h)) fun _ h => ⟨eo ▸ h.1, by rw [h.2.1, eo]⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀ (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) s ∧ VG.Proof.Pbkdf2.Md.AArch64.HmacInit.KR H s₀' (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.out s₀) s') (.block H.stream.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := VG.Proof.Pbkdf2.Md.AArch64.HmacInit.kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (c₁.seq (c₂.seq (keys.seq ((VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cmp_rel hH hp hp' hq si si').seq (mid.seq
    ((VG.Proof.Pbkdf2.Md.AArch64.HmacInit.cmp_rel hH hp hp' hq so so').seq restore))))))

end

/-- HMAC's `init` is verified against `initG`, given the taint checks. -/
theorem verified {sc : Nat} (hc : VG.Proof.Pbkdf2.Md.AArch64.HmacInit.Checks H) (hfit : H.stream.buf ≤ 8 * sc) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified AArch64.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => VG.Proof.Pbkdf2.Md.AArch64.HmacInit.correct hH (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.ct hH (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pre_of hH h₁ hfit) (VG.Proof.Pbkdf2.Md.AArch64.HmacInit.pre_of hH h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.HmacInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the functions, verified

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Core.lean`): what the kernel checks of a
hash function's code does not depend on its compression function or its
streaming functions, which our functions only call: `core H` is `H` with them
replaced by empty code, and `CoreOK` is what the kernel checks of `core H`
(the taint checks of the pieces between calls and that HMAC's buffers fit),
once for each hash function. How deeply frames nest in our functions follows
from the callees' (`hmacInit_fdepth`, …): ours push none. From them, HMAC's
`init` and `finalize`, `iterate` and `pbkdf2` are verified against the shared
contracts of `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`.

There is no stack pointer to check (`writesSp` is always `false` on AArch64),
so the artifacts' `spSafe` is `Code.all_of_forall`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG)
open VG.Proof.Pbkdf2.AArch64 (iterK iterImp)

/-- `H` without the functions it calls: its own code. -/
def core (H : Hash) : Hash :=
  ⟨H.P, H.D, H.W, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

/-! ## How deeply frames nest -/

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

section
variable {H : Hash}

theorem hmacInit_fdepth (hi : H.initC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) :
    H.hmacInit.aarch64Depth ≤ 1 := by
  simp only [Hash.hmacInit, Hash.stream, Hash.initKeys, Hash.keyLoop, Impl.Pbkdf2.Md.AArch64.Stream.callInit,
    Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, Code.aarch64Depth,
    VG.Proof.Pbkdf2.Md.AArch64.fdepth_of_noFrames hc]
  omega

theorem hmacFin_fdepth (hf : H.finC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) :
    H.hmacFin.aarch64Depth ≤ 1 := by
  simp only [Hash.hmacFin, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.callFin, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Code.aarch64Depth, VG.Proof.Pbkdf2.Md.AArch64.fdepth_of_noFrames hc]
  omega

theorem iterate_fdepth (hc : H.compC.noFrames = true) : H.iterate.aarch64Depth ≤ 1 := by
  simp only [Hash.iterate, Impl.Pbkdf2.AArch64.iterate, Impl.Pbkdf2.AArch64.main,
    Impl.Pbkdf2.AArch64.body, Impl.Pbkdf2.AArch64.compressBlock, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Code.aarch64Depth, VG.Proof.Pbkdf2.Md.AArch64.fdepth_of_noFrames hc]
  omega

end

/-! ## The taint checks, which look only at the own code -/

theorem HmacInit.Checks.of_core {H : Hash} (h : HmacInit.Checks (VG.Proof.Pbkdf2.Md.AArch64.core H)) : HmacInit.Checks H :=
  ⟨h.pro, h.argI, h.keys, h.mid, h.restore⟩

theorem HmacFin.Checks.of_core {H : Hash} (h : HmacFin.Checks (VG.Proof.Pbkdf2.Md.AArch64.core H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem Pbk.Checks.of_core {H : Hash} (h : Pbk.Checks (VG.Proof.Pbkdf2.Md.AArch64.core H)) : Pbk.Checks H :=
  ⟨h.entry, h.hk1, h.hk3, h.hk5, h.hk7, h.keyShr, h.keySub, h.short, h.su1, h.su3, h.loopRegs,
    h.pieceA, h.finArgs, h.pieceC, h.tail, h.exit⟩

/-- What the kernel checks of a hash function's own code (`core H`): the
taint checks of the pieces between calls, and that HMAC's buffers fit in
the working space. -/
structure CoreOK (C : Hash) : Prop where
  pbk : Pbk.Checks C
  iter : VG.Proof.Pbkdf2.AArch64.Checks C.P C.D
  hinit : HmacInit.Checks C
  hfin : HmacFin.Checks C
  /-- HMAC's buffers fit in the working space. -/
  fitI : C.stream.buf ≤ 8 * C.W
  fitF : C.stream.buf + C.stream.F ≤ 8 * C.W

/-! ## The functions, verified -/

/-- A state satisfying `pbkdf2`'s precondition, with `8 sc` bytes of scratch
space: an empty password, salt and output, and `c = 1`. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x4 => 1 | .x5 => 0x30000 | .x7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩]
  wr := [⟨0x30000, 0⟩, ⟨0x40000, sc * 8⟩]

/-- A state satisfying the precondition of `pbkdf2` with its working space on
the stack: `pbkSat` without the working space. -/
def pbkFrameSat : State := { VG.Proof.Pbkdf2.Md.AArch64.pbkSat 0 with wr := [⟨0x30000, 0⟩] }

section
variable {H : Hash} (hH : HashOK H) (C : VG.Proof.Pbkdf2.Md.AArch64.CoreOK (VG.Proof.Pbkdf2.Md.AArch64.core H))
include hH C

theorem hmacInit_ok (hsat : ∃ s, (Spec.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (initG hH.SH H.W) :=
  HmacInit.verified hH (HmacInit.Checks.of_core C.hinit) C.fitI (initImp _ _ hsat).sat_left

theorem hmacFin_ok (hsat : ∃ s, (Spec.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (finG hH.SH H.W) :=
  HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) C.fitF
    (finImp _ _ hsat).sat_left

theorem iterate_ok (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (iterK hH.SH H.W) :=
  VG.Proof.Pbkdf2.AArch64.verified hH.iterOk C.iter hH.comp (iterImp _ _ hsat).sat_left

/-- HMAC's `init`, verified against the shared contract. -/
theorem hmacInit_verified (hsat : ∃ s, (Spec.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (Spec.Hmac.initScratchContract hH.SH H.W AArch64.abi 16) :=
  (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_ok hH C hsat).of_implies (initImp _ _ hsat)

/-- HMAC's `finalize`, verified against the shared contract. -/
theorem hmacFin_verified (hsat : ∃ s, (Spec.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (Spec.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16) :=
  (VG.Proof.Pbkdf2.Md.AArch64.hmacFin_ok hH C hsat).of_implies (finImp _ _ hsat)

/-- `iterate`, verified against the shared contract. -/
theorem iterate_verified (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi) :=
  (VG.Proof.Pbkdf2.Md.AArch64.iterate_ok hH C hsat).of_implies (iterImp _ _ hsat)

/-- `pbkdf2`, verified against the shared contract. -/
theorem pbkdf2_verified
    (hsI : ∃ s, (Spec.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s)
    (hsF : ∃ s, (Spec.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16).pre s)
    (hsT : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s)
    (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) AArch64.abi 16).pre s) :
    Verified AArch64.target H.pbkdf2 (Spec.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) AArch64.abi 16) :=
  (Pbk.verified hH (Pbk.Checks.of_core C.pbk)
    (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_ok hH C hsI) (VG.Proof.Pbkdf2.Md.AArch64.hmacInit_fdepth hH.stream.initDepth hH.comp.noFrames)
    (VG.Proof.Pbkdf2.Md.AArch64.hmacFin_ok hH C hsF) (VG.Proof.Pbkdf2.Md.AArch64.hmacFin_fdepth hH.stream.finDepth hH.comp.noFrames)
    (VG.Proof.Pbkdf2.Md.AArch64.iterate_ok hH C hsT) (VG.Proof.Pbkdf2.Md.AArch64.iterate_fdepth hH.comp.noFrames)
    (pbkImp _ _ hsat).sat_left).of_implies (pbkImp _ _ hsat)

end

end VG.Proof.Pbkdf2.Md.AArch64

end
