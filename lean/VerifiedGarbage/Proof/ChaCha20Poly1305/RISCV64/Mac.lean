module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Prologue
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Poly1305.RISCV64.Buffer
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64

/-!
# ChaCha20-Poly1305 on RISC-V: the parts with calls

The one-time key (`keyGen`), the Poly1305 state for it (`polyInit`), the MAC
of the additional data (`macAad`), the encryption (`crypt`) and the MAC of
the ciphertext and the tag (`macData`): each from the state it starts in, to
what it leaves and the regions it writes (`Step`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt leBytes mac Buffered Repr)
open VG.Spec.ChaCha20 (stateAt initState)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-! ## Regions and covers -/

theorem covers_right {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-- Parts of the context are in the working space. -/
theorem covers_ctx {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r.base = off (cx s₀) k ∧ k + r.len ≤ 608) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hb, hk⟩ := h r hr
  have := pad_lt' s₀
  exact ⟨wR s₀, by rw [hwr]; exact hp.w_wr, pad (wk s₀) + k, by rw [hb, cx_off], by show _ ≤ 616; omega⟩

theorem cx_zero (s₀ : State) : cx s₀ = off (cx s₀) 0 := (off_zero _).symm

/-- The context is 4-byte aligned, and so is it plus a multiple of 8. -/
theorem cx_al4 (s₀ : State) : (cx s₀).toNat % 4 = 0 := by
  have := cx_al s₀ (d := 0) (by decide); rw [off_zero] at this; omega

theorem off_al4 (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (off (cx s₀) d).toNat % 4 = 0 := by
  have := cx_al s₀ hd; omega

/-- `ctx[0, 64)` as a part. -/
theorem st_sub (s₀ : State) : (⟨cx s₀, 64⟩ : Region) = sub s₀ 0 64 := by rw [sub, ← cx_zero]

/-! ## The one-time key -/

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

theorem keyGen_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = cx s₀)
    (hst : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)) :
    WP isa keyGen s fun s' => Step [sub s₀ 64 256] s s' ∧ s'.gpr .a0 = cx s₀ ∧
      bytesAt s'.mem (off (cx s₀) 64) 32 = otk s₀ := by
  refine WP.seq (wp_addi (imm := bufOff) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have a0₁ : s₁.gpr .a0 = cx s₀ := by rw [u₁.other _ (by decide), ha]
  refine block_call a0₁ (B := off (cx s₀) 64) (hSa := cx_al4 s₀) (hBa := off_al4 s₀ (by decide)) (by rw [u₁.gpr, ha]; rfl)
    (Offset.disjoint_base (cx s₀) (d := 64) (n := 256) (k := 64) (by decide) (by decide)) ?_ ?_ fun s' k hb => ?_
  · refine covers_right (covers_ctx hp (by rw [u₁.wr, h.wr]) _ fun r hr => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, cx_zero s₀, by show 0 + 64 ≤ 608; decide⟩, ⟨64, rfl, by show 64 + 256 ≤ 608; decide⟩]
  · refine covers_ctx hp (by rw [u₁.wr, h.wr]) _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨64, rfl, by show 64 + 256 ≤ 608; decide⟩
  refine ⟨(Step.upd _ u₁).trans k.step, by rw [k.a0, a0₁], ?_⟩
  rw [bytesAt_serialize _ _ (by decide), hb, u₁.mem, hst]
  rfl

/-! ## The Poly1305 state -/

theorem polyInit_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = cx s₀)
    (hk : bytesAt s.mem (off (cx s₀) 64) 32 = otk s₀) :
    WP isa polyInit s fun s' => Step [sub s₀ polyOff 128] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      Repr s'.mem (ps s₀) (otk s₀) [] := by
  refine WP.seq (wp_addi (imm := bufOff) (by decide) fun s₁ u₁ =>
    wp_addi (imm := polyOff) (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have hw : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  refine init_call (P := ps s₀) (K := off (cx s₀) 64) (by rw [u₂.gpr, u₁.other _ (by decide), ha])
    (by rw [u₂.other _ (by decide), u₁.gpr, ha]; rfl) (sub_disj s₀ (a := polyOff) (n := 128) (b := 64) (m := 32) (by decide) (by decide) (by decide))
    ?_ ?_ fun s' k hr => ?_
  · refine covers_right (covers_ctx hp hw _ fun r hr => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨64, rfl, by show 64 + 32 ≤ 608; decide⟩, ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩]
  · refine covers_ctx hp hw _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩
  refine ⟨((Step.upd _ u₁).trans (Step.upd _ u₂)).trans k.step,
    by rw [k.a0, u₂.gpr, u₁.other _ (by decide), ha], ?_⟩
  rw [u₂.mem, u₁.mem, hk] at hr
  exact hr


/-! ## Padding -/

theorem covers_one {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun a n ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨r', h, hc⟩

/-- `-x mod 16`, as `padArgs` computes it. -/
theorem padN (x : BitVec 64) :
    (BitVec.ofNat 64 0 - x) &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 ((16 - x.toNat % 16) % 16) := by
  rw [Proof.Poly1305.RISCV64.and15]
  congr 1
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The zeros of the context are the padding of `x`. -/
theorem zeros_pad {m : Mem} {p : Addr} (x : List Byte) (hz : ∀ i < 16, m (p + BitVec.ofNat 64 i) = 0) :
    bytesAt m p ((16 - x.length % 16) % 16) = pad16 x := by
  unfold pad16
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    rw [Nat.mod_eq_of_lt (by omega)]
    apply List.ext_getElem (by simp [Proof.Poly1305.length_bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hz i (by simp [bytesAt] at h₁; omega)

theorem zeros_of {s₀ : State} {m : Mem} (hz : ∀ i < 16, m (off (cx s₀) (zeroOff + i)) = 0) :
    ∀ i < 16, m (off (cx s₀) zeroOff + BitVec.ofNat 64 i) = 0 := fun i hi => by
  rw [Offset.add_add]; exact hz i hi

theorem ps_add (s₀ : State) (d : Nat) : ps s₀ + BitVec.ofNat 64 d = off (cx s₀) (polyOff + d) :=
  Offset.add_add _ _ _

theorem a3_eq (s₀ : State) : s₀.gpr .a3 = BitVec.ofNat 64 (AL s₀) := by simp

theorem a5_eq (s₀ : State) : s₀.gpr .a5 = BitVec.ofNat 64 (L s₀) := by simp

/-! ## The MAC of the additional data -/

theorem macAad_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    (hb : Buffered s.mem (ps s₀) (otk s₀) [])
    (hz : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0) :
    WP isa macAad s fun s' => Step [sub s₀ polyOff 128] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      Buffered s'.mem (ps s₀) (otk s₀)
        (bytesAt s.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s.mem (ad s₀) (AL s₀))) := by
  unfold macAad update padArgs
  simp only [mov]
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_)
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  have r₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hP : (sub s₀ polyOff 128).Disjoint (aR s₀) := (APre.w_sub (s₀ := s₀) hp.a_w (k := polyOff) (n := 128) (by decide)).symm
  have cP : Covers [sub s₀ polyOff 128] s₃.wr := covers_ctx hp w₃ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := ad s₀) (c := BitVec.ofNat 64 0) (n := AL s₀)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.regs.s7])
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s8, a3_eq])
    (s₀.gpr .a3).isLt hP
    (Covers.append (covers_one (r := aR s₀) (rs := s₃.rd) (by rw [r₃]; exact hp.a_rd)) cP) cP
    fun s₄ k₄ hb₄ => ?_)
  refine WP.seq (wp_mv fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ =>
    wp_andi (by decide) fun s₈ u₈ => wp_addi (imm := zeroOff - polyOff) (by decide) fun s₉ u₉ =>
    WP.block_nil ?_)
  have hnl : (16 - AL s₀ % 16) % 16 < 16 := Nat.mod_lt _ (by decide)
  have w₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, k₄.wr, w₃]
  have r₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, k₄.rd, r₃]
  have a0₈ : s₈.gpr .a0 = ps s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), k₄.a0,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha]
  have s8₄ : s₄.gpr .s8 = s₀.gpr .a3 := by
    rw [k₄.cs _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.regs.s8]
  have cP' : Covers [sub s₀ polyOff 128] s₉.wr := covers_ctx hp w₉ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩
  refine update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := off (cx s₀) zeroOff) (c := s₀.gpr .a3)
    (n := (16 - AL s₀ % 16) % 16) (by rw [u₉.other _ (by decide), a0₈])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, s8₄])
    (by rw [u₉.gpr, a0₈, ps_add]; rfl)
    (by rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      s8₄, padN])
    (by omega) (sub_disj s₀ (a := polyOff) (n := 128) (b := zeroOff) (m := (16 - AL s₀ % 16) % 16)
      (by simp only [polyOff, zeroOff]; omega) (by decide) (by simp only [zeroOff]; omega))
    (covers_right (covers_ctx hp w₉ _ fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨zeroOff, rfl, by show zeroOff + _ ≤ 608; simp only [zeroOff]; omega⟩
      · exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩)) cP' fun s' k' hb' => ?_
  refine ⟨?_, by rw [k'.a0, u₉.other _ (by decide), a0₈], ?_⟩
  · refine ((((((((Step.upd _ u₁).trans (Step.upd _ u₂)).trans (Step.upd _ u₃)).trans k₄.step).trans
      (Step.upd _ u₅)).trans (Step.upd _ u₆)).trans (Step.upd _ u₇)).trans (Step.upd _ u₈)).trans
      ((Step.upd _ u₉).trans k'.step)
  · have hA : bytesAt s₃.mem (ad s₀) (AL s₀) = bytesAt s.mem (ad s₀) (AL s₀) := by rw [m₃]
    have b₄ := hb₄ (otk s₀) [] (by rw [m₃]; exact hb) (by simp)
    rw [List.nil_append, hA] at b₄
    have b' := hb' (otk s₀) _ (by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact b₄)
      (by rw [Proof.Poly1305.length_bytesAt])
    have hz₄ : ∀ i < 16, s₉.mem (off (cx s₀) zeroOff + BitVec.ofNat 64 i) = 0 := zeros_of fun i hi => by
      rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem,
        byte_sub s₀ (k := polyOff) (n := 128) k₄.frame (by simp only [polyOff, zeroOff]; omega) (by decide)
          (by simp only [zeroOff]; omega), m₃]
      exact hz i hi
    have hp16 := zeros_pad (bytesAt s.mem (ad s₀) (AL s₀)) hz₄
    rw [Proof.Poly1305.length_bytesAt] at hp16
    rw [hp16] at b'
    exact b'


/-! ## The encryption -/

/-- The ChaCha20 state for counter 0, with the low byte of the counter set to 1. -/
theorem stateAt_ctr1 {m : Mem} {p : Addr} {key nonce : List Byte}
    (h : stateAt m p = initState key 0 nonce) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) (BitVec.ofNat 8 1)) p = initState key 1 nonce := by
  have hc : initState key 1 nonce = Proof.ChaCha20.ctr (initState key 0 nonce) 1 := by
    rw [ctr_initState]; rfl
  have h12 : m.readW (p + BitVec.ofNat 64 48) 32 = 0 := by
    have := congrArg (·[12]) h
    simpa [stateAt, initState] using this
  rw [hc, ← h]
  apply Vector.ext; intro i hi
  simp only [stateAt, Proof.ChaCha20.ctr, Vector.getElem_set, Vector.getElem_ofFn]
  split
  · rename_i e; subst e
    show (m.writeW _ _).readW (p + BitVec.ofNat 64 48) 32 = m.readW (p + BitVec.ofNat 64 48) 32 + _
    rw [h12]
    refine Proof.ChaCha20.word_ext fun j hj => ?_
    rw [← Mem.readW_byte _ _ hj, WriteBytes.writeW8_apply, Offset.add_add]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp
    all_goals
      split
      · exact absurd ‹_› (Offset.add_ofNat_ne p (by decide) (by decide) (by decide))
      · rw [← Offset.add_add p 48, Mem.readW_byte m (p + BitVec.ofNat 64 48) (by decide), h12]
        decide
  · rename_i e
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by decide)) (by decide)

theorem fit_d' (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .a5).isLt

theorem crypt_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    (hst : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Step [sub s₀ 0 64, dR s₀, sub s₀ 64 320] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold crypt
  simp only [mov]
  refine WP.seq (wp_subi (imm := polyOff) (by decide) fun s₁ u₁ => wp_li (imm := 1) (by decide) fun s₂ u₂ => ?_)
  have a0₁ : s₁.gpr .a0 = cx s₀ := by rw [u₁.gpr, ha, ps, BitVec.add_sub_cancel]
  refine wp_sb (a := off (cx s₀) 48) (by decide) (by rw [u₂.other _ (by decide), a0₁])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.in_w (by decide)) fun s₃ g₃ => ?_
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_addi (imm := bufOff) (by decide) fun s₆ u₆ =>
    WP.block_nil ?_
  have m₆ : s₆.mem = s.mem.writeW (off (cx s₀) 48) (BitVec.ofNat 8 1) := by
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, VG.RISCV64.Bytes.setWidth_ofNat_byte, u₂.mem, u₁.mem]
  have f₆ : Frame [sub s₀ 0 64] s.mem s₆.mem := by
    rw [m₆]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 8 / 8) (by decide) (by decide) (by decide))
  have a0₆ : s₆.gpr .a0 = cx s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      a0₁]
  have g₆ : ∀ r, r ≠ .a0 → r ≠ .t0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₆.gpr r = s.gpr r :=
    fun r h0 ht h1 h2 h3 => by
      rw [u₆.other r h3, u₅.other r h2, u₄.other r h1, g₃.gpr, u₂.other r ht, u₁.other r h0]
  have w₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  have hS : (⟨cx s₀, 64⟩ : Region).Disjoint (dR s₀) := by
    rw [st_sub]; exact (APre.w_sub (s₀ := s₀) hp.d_w (k := 0) (n := 64) (by decide)).symm
  have hcov : Covers [⟨cx s₀, 64⟩, dR s₀, sub s₀ 64 320] s₆.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨wR s₀, by rw [w₆]; exact hp.w_wr, pad (wk s₀), rfl, by show pad (wk s₀) + 64 ≤ 616; omega⟩
    · exact ⟨dR s₀, by rw [w₆]; exact hp.d_wr, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨wR s₀, by rw [w₆]; exact hp.w_wr, pad (wk s₀) + 64, cx_off s₀ 64,
        by show pad (wk s₀) + 64 + 320 ≤ 616; omega⟩
  refine WP.seq (xor_call (S := cx s₀) (D := dp s₀) (n := L s₀) (B := off (cx s₀) 64)
    (hSa := cx_al4 s₀) (hBa := off_al4 s₀ (by decide)) a0₆
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.regs.s9])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.regs.s10, a5_eq])
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide), a0₁]; rfl)
    (fit_d' s₀) hS (Offset.base_disjoint (cx s₀) (k := 64) (e := 64) (n := 320) (by decide) (by decide))
    (APre.w_sub (s₀ := s₀) hp.d_w (k := 64) (n := 320) (by decide)) hp.fit_d
    (covers_right (by rw [List.nil_append]; exact hcov)) hcov fun s₇ k₇ hx => ?_)
  refine wp_addi (imm := polyOff) (by decide) fun s₈ u₈ => WP.block_nil ?_
  refine ⟨?_, by rw [u₈.gpr, k₇.a0, a0₆], ?_⟩
  · have st₆ : Step [sub s₀ 0 64, dR s₀, sub s₀ 64 320] s s₆ :=
      ⟨fun r hr => g₆ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide),
        by rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp], by rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd],
        by rw [w₆, h.wr], f₆.mono (by simp)⟩
    refine (st₆.trans ?_).trans (Step.upd _ u₈)
    have := k₇.step
    rw [st_sub] at this
    exact this
  · have hd : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact APre.w_sub (s₀ := s₀) hp.d_w (k := 0) (n := 64) (by decide)) (Nat.le_of_lt (fit_d' s₀))
    have hs : stateAt s₆.mem (cx s₀) = initState (K s₀) 1 (N s₀) := by rw [m₆]; exact stateAt_ctr1 hst
    rw [u₈.mem]
    show Spec.ChaCha20.bytesAt _ _ _ = _
    rw [hx, hs, encrypt_eq, show (bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      Proof.Poly1305.length_bytesAt _ _ _]
    exact congrArg (fun x => List.zipWith _ x _) hd


/-! ## The MAC of the ciphertext and the tag -/

/-- `round16` leaves a multiple of 16. -/
theorem round16_mod (x : BitVec 64) : ((x + BitVec.ofNat 64 15) &&& BitVec.ofInt 64 (-16)).toNat % 16 = 0 := by
  rw [BitVec.toNat_and, show (16 : Nat) = 2 ^ 4 from rfl, Nat.and_mod_two_pow,
    show (BitVec.ofInt 64 (-16)).toNat % 2 ^ 4 = 0 from rfl, Nat.and_zero]

theorem add_mod16 (a b : BitVec 64) : (a + b).toNat % 16 = (a.toNat + b.toNat) % 16 := by
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]

theorem length_pad16 (x : List Byte) : (x ++ pad16 x).length % 16 = 0 := by
  unfold pad16; split <;> simp <;> omega

theorem covers_wr2 {r₁ r₂ : Region} {rd wr : List Region} (h₁ : r₁ ∈ wr) (h₂ : Covers [r₂] wr) :
    Covers ([r₁] ++ [r₂]) (rd ++ wr) := fun a n ⟨r, hr, hc⟩ => by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨r, List.mem_append_right _ h₁, hc⟩
  · obtain ⟨r', hr', hc'⟩ := h₂ a n ⟨r, List.mem_singleton_self _, hc⟩
    exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem Step.upd' {rs : List Region} {s s₁ s₂ : State} (h : Step rs s s₁) {d : Reg} {v : BitVec 64}
    (u : Upd s₁ s₂ d v) (hd : d ∉ preserved := by decide) : Step rs s s₂ :=
  h.trans (Step.upd rs u hd)

theorem length_leBytes (n x : Nat) : (leBytes n x).length = n := by simp [leBytes]

/-- The invariant survives an instruction writing a temporary register. -/
theorem Inv.upd {s₀ s s' : State} (h : Inv s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ preserved := by decide) : Inv s₀ s' :=
  h.step (Step.upd [] u hd) (by simp) (by simp)

/-- The data, the padding and the lengths after `M`, and the tag at `O`, which
`out` puts in `a2`. -/
theorem macData_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    {M : List Byte} (hb : Buffered s.mem (ps s₀) (otk s₀) M) (hM : M.length % 16 = 0)
    (hz : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0)
    (hl : bytesAt s.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))
    {out : Instr} {O : Addr}
    (hout : ∀ s : State, Inv s₀ s → s.gpr .a0 = ps s₀ → ∀ Q : State → Prop,
      (∀ s', Upd s s' .a2 O → Q s') → WP isa (.block [out]) s Q)
    (hPO : (sub s₀ polyOff 128).Disjoint ⟨O, 16⟩) (hOw : Covers [sub s₀ polyOff 128, ⟨O, 16⟩] s₀.wr) :
    WP isa (macData out) s fun s' => Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      bytesAt s'.mem O 16 = mac (otk s₀) (M ++ (bytesAt s.mem (dp s₀) (L s₀) ++
        pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))) := by
  unfold macData update round16 padArgs
  simp only [mov, List.cons_append, List.nil_append]
  have cP : ∀ s' : State, s'.wr = s₀.wr → Covers [sub s₀ polyOff 128] s'.wr := fun s' hw =>
    covers_ctx hp hw _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩
  have hdP : (sub s₀ polyOff 128).Disjoint (dR s₀) :=
    (APre.w_sub (s₀ := s₀) hp.d_w (k := polyOff) (n := 128) (by decide)).symm
  -- The data.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ =>
    wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_)
  have i₄ : Inv s₀ s₄ := (((h.upd u₁).upd u₂).upd u₃).upd u₄
  have a0₄ : s₄.gpr .a0 = ps s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ : (s₄.gpr .a1).toNat % 16 = 0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; exact round16_mod _
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := dp s₀) (c := s₄.gpr .a1) (n := L s₀) a0₄ rfl
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s9])
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s10, a5_eq])
    (fit_d' s₀) hdP
    (covers_wr2 (by rw [i₄.wr]; exact hp.d_wr) (cP s₄ i₄.wr)) (cP s₄ i₄.wr) fun s₅ k₅ hb₅ => ?_)
  have i₅ : Inv s₀ s₅ := i₄.step1 k₅.step (k := polyOff) (n := 128) (by decide)
  have a0₅ : s₅.gpr .a0 = ps s₀ := by rw [k₅.a0, a0₄]
  have B₅ := hb₅ (otk s₀) M (by rw [m₄]; exact hb) (c₄.trans hM.symm)
  rw [m₄] at B₅
  have st₅ : Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s₅ :=
    ((((Step.refl _ s).upd' u₁).upd' u₂).upd' u₃).upd' u₄ |>.trans (k₅.step.mono (by simp))
  -- The padding of the data.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₆ u₆ => wp_andi (by decide) fun s₇ u₇ =>
    wp_add fun s₈ u₈ => wp_li (imm := 0) (by decide) fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ =>
    wp_andi (by decide) fun s₁₁ u₁₁ => wp_addi (imm := zeroOff - polyOff) (by decide) fun s₁₂ u₁₂ =>
    WP.block_nil ?_)
  have i₁₂ : Inv s₀ s₁₂ := ((((((i₅.upd u₆).upd u₇).upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂
  have a0₁₂ : s₁₂.gpr .a0 = ps s₀ := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a0₅]
  have m₁₂ : s₁₂.mem = s₅.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have hnl : (16 - L s₀ % 16) % 16 < 16 := Nat.mod_lt _ (by decide)
  have c₁₂ : (s₁₂.gpr .a1).toNat % 16 = (M ++ bytesAt s.mem (dp s₀) (L s₀)).length % 16 := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), add_mod16, i₅.regs.s10, a5_eq,
      toNat_ofNat_lt (fit_d' s₀), List.length_append, Proof.Poly1305.length_bytesAt]
    have := round16_mod (s₅.gpr .s8)
    omega
  have a2₁₂ : s₁₂.gpr .a2 = off (cx s₀) zeroOff := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a0₅, ps_add]
    rfl
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := off (cx s₀) zeroOff) (c := s₁₂.gpr .a1)
    (n := (16 - L s₀ % 16) % 16) a0₁₂ rfl a2₁₂
    (by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), i₅.regs.s10, padN])
    (by omega) (sub_disj s₀ (a := polyOff) (n := 128) (b := zeroOff) (m := (16 - L s₀ % 16) % 16)
      (by simp only [polyOff, zeroOff]; omega) (by decide) (by simp only [zeroOff]; omega))
    (covers_right (covers_ctx hp i₁₂.wr _ fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨zeroOff, rfl, by show zeroOff + _ ≤ 608; simp only [zeroOff]; omega⟩
      · exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩)) (cP s₁₂ i₁₂.wr) fun s₁₃ k₁₃ hb₁₃ => ?_)
  have i₁₃ : Inv s₀ s₁₃ := i₁₂.step1 k₁₃.step (k := polyOff) (n := 128) (by decide)
  have a0₁₃ : s₁₃.gpr .a0 = ps s₀ := by rw [k₁₃.a0, a0₁₂]
  have hz₁₂ : ∀ i < 16, s₁₂.mem (off (cx s₀) zeroOff + BitVec.ofNat 64 i) = 0 := zeros_of fun i hi => by
    rw [m₁₂, byte_sub s₀ (k := polyOff) (n := 128) k₅.frame (by simp only [polyOff, zeroOff]; omega)
      (by decide) (by simp only [zeroOff]; omega), m₄]
    exact hz i hi
  have hp16 := zeros_pad (bytesAt s.mem (dp s₀) (L s₀)) hz₁₂
  rw [Proof.Poly1305.length_bytesAt] at hp16
  have B₁₃ := hb₁₃ (otk s₀) _ (by rw [m₁₂]; exact B₅) c₁₂
  rw [hp16] at B₁₃
  have st₁₃ : Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s₁₃ :=
    ((((((((st₅.upd' u₆).upd' u₇).upd' u₈).upd' u₉).upd' u₁₀).upd' u₁₁).upd' u₁₂).trans
      (k₁₃.step.mono (by simp)))
  -- The lengths block.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₁₄ u₁₄ => wp_andi (by decide) fun s₁₅ u₁₅ =>
    wp_addi (imm := 15) (by decide) fun s₁₆ u₁₆ => wp_andi (by decide) fun s₁₇ u₁₇ =>
    wp_add fun s₁₈ u₁₈ => wp_addi (imm := lenOff - polyOff) (by decide) fun s₁₉ u₁₉ =>
    wp_li (imm := 16) (by decide) fun s₂₀ u₂₀ => WP.block_nil ?_)
  have i₂₀ : Inv s₀ s₂₀ := ((((((i₁₃.upd u₁₄).upd u₁₅).upd u₁₆).upd u₁₇).upd u₁₈).upd u₁₉).upd u₂₀
  have a0₂₀ : s₂₀.gpr .a0 = ps s₀ := by
    rw [u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), a0₁₃]
  have m₂₀ : s₂₀.mem = s₁₃.mem := by
    rw [u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem]
  have hM₁₃ : (M ++ bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀))).length % 16 = 0 := by
    have := length_pad16 (bytesAt s.mem (dp s₀) (L s₀))
    rw [List.append_assoc, List.length_append]; omega
  have c₂₀ : (s₂₀.gpr .a1).toNat % 16 = 0 := by
    rw [u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.gpr, u₁₄.gpr, u₁₇.gpr, u₁₆.gpr, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), add_mod16]
    have := round16_mod (s₁₃.gpr .s8)
    have := round16_mod (s₁₃.gpr .s10)
    omega
  have a2₂₀ : s₂₀.gpr .a2 = off (cx s₀) lenOff := by
    rw [u₂₀.other _ (by decide), u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), a0₁₃, ps_add]
    rfl
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := off (cx s₀) lenOff) (c := s₂₀.gpr .a1) (n := 16) a0₂₀ rfl
    a2₂₀ u₂₀.gpr (by decide) (sub_disj s₀ (a := polyOff) (n := 128) (b := lenOff) (m := 16) (by decide) (by decide)
      (by decide))
    (covers_right (covers_ctx hp i₂₀.wr _ fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨lenOff, rfl, by show lenOff + 16 ≤ 608; decide⟩
      · exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 608; decide⟩)) (cP s₂₀ i₂₀.wr) fun s₂₁ k₂₁ hb₂₁ => ?_)
  have i₂₁ : Inv s₀ s₂₁ := i₂₀.step1 k₂₁.step (k := polyOff) (n := 128) (by decide)
  have a0₂₁ : s₂₁.gpr .a0 = ps s₀ := by rw [k₂₁.a0, a0₂₀]
  have hl₂₀ : bytesAt s₂₀.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    have d : ∀ r ∈ [(⟨ps s₀, 128⟩ : Region)], (⟨off (cx s₀) lenOff, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (a := lenOff) (n := 16) (b := polyOff) (m := 128) (by decide) (by decide) (by decide)
    rw [m₂₀, bytesAt_frame k₁₃.frame d (by decide), m₁₂, bytesAt_frame k₅.frame d (by decide), m₄, hl]
  have B₂₁ := hb₂₁ (otk s₀) _ (by rw [m₂₀]; exact B₁₃) (by rw [c₂₀, hM₁₃])
  rw [hl₂₀] at B₂₁
  have st₂₁ : Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s₂₁ :=
    (((((((st₁₃.upd' u₁₄).upd' u₁₅).upd' u₁₆).upd' u₁₇).upd' u₁₈).upd' u₁₉).upd' u₂₀).trans
      (k₂₁.step.mono (by simp))
  -- The tag.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₂₂ u₂₂ => wp_andi (by decide) fun s₂₃ u₂₃ =>
    wp_addi (imm := 15) (by decide) fun s₂₄ u₂₄ => wp_andi (by decide) fun s₂₅ u₂₅ =>
    wp_add fun s₂₆ u₂₆ => wp_addi (imm := 16) (by decide) fun s₂₇ u₂₇ => ?_)
  have i₂₇ : Inv s₀ s₂₇ := (((((i₂₁.upd u₂₂).upd u₂₃).upd u₂₄).upd u₂₅).upd u₂₆).upd u₂₇
  have a0₂₇ : s₂₇.gpr .a0 = ps s₀ := by
    rw [u₂₇.other _ (by decide), u₂₆.other _ (by decide), u₂₅.other _ (by decide), u₂₄.other _ (by decide),
      u₂₃.other _ (by decide), u₂₂.other _ (by decide), a0₂₁]
  refine hout s₂₇ i₂₇ a0₂₇ _ fun s₂₈ u₂₈ => ?_
  have i₂₈ : Inv s₀ s₂₈ := i₂₇.upd u₂₈
  have c₂₈ : (s₂₈.gpr .a1).toNat % 16 = 0 := by
    rw [u₂₈.other _ (by decide), u₂₇.gpr, u₂₆.gpr, u₂₅.other _ (by decide), u₂₄.other _ (by decide), u₂₃.gpr,
      u₂₂.gpr, u₂₅.gpr, u₂₄.gpr, u₂₃.other _ (by decide), u₂₂.other _ (by decide), add_mod16,
      toNat_ofNat_lt (by decide : 16 < 2 ^ 64)]
    have := round16_mod (s₂₁.gpr .s8)
    have := round16_mod (s₂₁.gpr .s10)
    have := add_mod16 ((s₂₁.gpr .s8 + BitVec.ofNat 64 15) &&& BitVec.ofInt 64 (-16))
      ((s₂₁.gpr .s10 + BitVec.ofNat 64 15) &&& BitVec.ofInt 64 (-16))
    omega
  have m₂₈ : s₂₈.mem = s₂₁.mem := by
    rw [u₂₈.mem, u₂₇.mem, u₂₆.mem, u₂₅.mem, u₂₄.mem, u₂₃.mem, u₂₂.mem]
  refine finalize_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (O := O) (c := s₂₈.gpr .a1) (by rw [u₂₈.other _ (by decide), a0₂₇]) rfl
    u₂₈.gpr hPO (by rw [List.nil_append]; exact covers_right (by rw [i₂₈.wr]; exact hOw))
    (by rw [i₂₈.wr]; exact hOw) fun s' k' ht => ?_
  refine ⟨((((((((st₂₁.upd' u₂₂).upd' u₂₃).upd' u₂₄).upd' u₂₅).upd' u₂₆).upd' u₂₇).upd' u₂₈).trans k'.step),
    by rw [k'.a0, u₂₈.other _ (by decide), a0₂₇], ?_⟩
  rw [ht (otk s₀) _ (by rw [m₂₈]; exact B₂₁) (by
    simp only [c₂₈, List.length_append, length_leBytes]
    simp only [List.length_append] at hM₁₃; omega)]
  simp only [List.append_assoc]

end VG.Proof.ChaCha20Poly1305.RISCV64
