module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Mac
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Range

/-!
# ChaCha20-Poly1305 on RISC-V: correctness

`seal` and `open` from their parts: the prologue, the calls, and the
epilogue, which restores our caller's registers (and, in `open`, compares
the tags without a branch).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt leBytes mac Buffered Repr)
open VG.Spec.ChaCha20 (stateAt initState)
open VG.Spec.ChaCha20Poly1305 (pad16 polyKeyGen)

variable {e : Bool}

/-! ## Memory through the parts -/

/-- A byte of a part of the context through a frame apart from it. -/
theorem byte_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {k n : Nat}
    (hd : ∀ r ∈ rs, (sub s₀ k n).Disjoint r) (hn : k + n ≤ 608) {i : Nat} (hi : i < n) :
    m' (off (cx s₀) (k + i)) = m (off (cx s₀) (k + i)) := by
  have := hf.bytes (R := sub s₀ k n) hd (by show n ≤ 2 ^ 64; omega) hi
  rwa [Offset.add_add] at this

/-- The parts of the context are apart from each other. -/
theorem parts_disj (s₀ : State) {k n : Nat} (rs : List (Nat × Nat))
    (h : ∀ p ∈ rs, (p.1 + p.2 ≤ k ∨ k + n ≤ p.1) ∧ p.1 + p.2 ≤ 608) (hk : k + n ≤ 608) :
    ∀ r ∈ rs.map (fun p => sub s₀ p.1 p.2), (sub s₀ k n).Disjoint r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact sub_disj s₀ (h p hp).1.symm hk (h p hp).2

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.a_w
    · exact hp.a_d) (Nat.le_of_lt (s₀.gpr .a3).isLt)

/-- The received tag is unchanged. -/
theorem tag_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (tp s₀) 16 = T0 s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.t_w
    · exact hp.d_t.symm) (by decide)

/-! ## Restoring the registers -/

/-- The registers `restore` loads. -/
abbrev restored : List Reg := [.s7, .s8, .s9, .s10, .s11, .ra]

theorem restore_ok {s₀ : State} (hp : APre e s₀) {s : State} (ht : s.gpr .t0 = cx s₀) (hs : Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ restored, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ restored → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  have hin : ∀ d, d + 8 ≤ 48 → InRegions (s.rd ++ s.wr) (off (cx s₀) (savOff + d)) 8 := fun d hd => by
    rw [hrd, hwr]; exact hp.in_w' (by simp only [savOff]; omega)
  have hal : ∀ d, d % 8 = 0 → (off (cx s₀) (savOff + d)).toNat % 8 = 0 := fun d hd =>
    cx_al s₀ (by simp only [savOff]; omega)
  unfold restore
  refine wp_ld (a := off (cx s₀) savOff) (by decide) (by rw [ht]) (hal 0 (by decide))
    (by simpa using hin 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 8)) (by decide) (by rw [u₁.other _ (by decide), ht])
    (hal 8 (by decide)) (by rw [u₁.rd, u₁.wr]; exact hin 8 (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 16)) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), ht]) (hal 16 (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 16 (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 24)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht]) (hal 24 (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 24 (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 32)) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht])
    (hal 32 (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 32 (by decide)) fun s₅ u₅ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 40)) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), ht]) (hal 40 (by decide))
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 40 (by decide))
    fun s₆ u₆ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨fun r hr => ?_, fun r hr => ?_, by rw [u₆.mem, m₅], by
    rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, hs.s7]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, hs.s8]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        hs.s9]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hs.s10]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.s11]
    · rw [u₆.gpr, m₅, hs.ra]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h8, h9, h10, h11, hra⟩ := hr
    rw [u₆.other r hra, u₅.other r h11, u₄.other r h10, u₃.other r h9, u₂.other r h8, u₁.other r h7]

/-- The callee-saved registers on return, from those restored and those kept. -/
theorem abi_of {s₀ s s' : State} (h : Inv s₀ s)
    (hr : ∀ r ∈ restored, s'.gpr r = s₀.gpr r) (hk : ∀ r ∈ others, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s₀.sp) : abiPreserved s₀ s' := by
  refine ⟨fun r hr' => ?_, hsp, hr _ (by simp)⟩
  by_cases hm : r ∈ restored
  · exact hr r hm
  · have ho : r ∈ others := by revert r; decide
    rw [hk r ho, h.pres r ho]


/-! ## Up to the MAC of the additional data -/

/-- After the MAC of the additional data. -/
structure AfterAad (s₀ s : State) : Prop where
  inv : Inv s₀ s
  a0 : s.gpr .a0 = ps s₀
  fw : Frame [wR s₀] s₀.mem s.mem
  st : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)
  buf : Buffered s.mem (ps s₀) (otk s₀) (A s₀ ++ pad16 (A s₀))
  zero : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0
  lens : bytesAt s.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀)

theorem st_disj (s₀ : State) {k n : Nat} (h : 64 ≤ k) (hk : k + n ≤ 608) :
    ∀ r ∈ [sub s₀ k n], (⟨cx s₀, 64⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [st_sub]; exact sub_disj s₀ (.inl h) (by decide) hk

theorem head_ok {s₀ : State} (hp : APre e s₀) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s, AfterAad s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (save ++ moves ++ setup)) (.seq keyGen (.seq polyInit (.seq macAad rest)))) s₀ Q := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ p₁ => ?_)
  refine WP.seq (WP.mono (keyGen_ok hp p₁.inv p₁.a0 p₁.st) fun s₂ ⟨st₂, a₂, k₂⟩ => ?_)
  have i₂ := p₁.inv.step1 st₂ (by decide)
  refine WP.seq (WP.mono (polyInit_ok hp i₂ a₂ k₂) fun s₃ ⟨st₃, a₃, r₃⟩ => ?_)
  have i₃ := i₂.step1 st₃ (by decide)
  have hz : ∀ {m m' : Mem} {k n : Nat}, Frame [sub s₀ k n] m m' → (zeroOff + 16 ≤ k ∨ k + n ≤ zeroOff) →
      k + n ≤ 608 → ∀ i < 16, m' (off (cx s₀) (zeroOff + i)) = m (off (cx s₀) (zeroOff + i)) :=
    fun hf h hk i hi => byte_sub s₀ hf (by omega) hk (by simp only [zeroOff]; omega)
  have z₃ : ∀ i < 16, s₃.mem (off (cx s₀) (zeroOff + i)) = 0 := fun i hi => by
    rw [hz st₃.frame (by decide) (by decide) i hi, hz st₂.frame (by decide) (by decide) i hi, p₁.zero i hi]
  have b₃ : Buffered s₃.mem (ps s₀) (otk s₀) [] := ⟨r₃, rfl⟩
  refine WP.seq (WP.mono (macAad_ok hp i₃ a₃ b₃ z₃) fun s₄ ⟨st₄, a₄, b₄⟩ => k s₄ ?_)
  have i₄ := i₃.step1 st₄ (by decide)
  rw [aad_eq hp i₃] at b₄
  have hl : ∀ {m m' : Mem} {k n : Nat}, Frame [sub s₀ k n] m m' → (lenOff + 16 ≤ k ∨ k + n ≤ lenOff) →
      k + n ≤ 608 → bytesAt m' (off (cx s₀) lenOff) 16 = bytesAt m (off (cx s₀) lenOff) 16 :=
    fun hf h hk => bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (a := lenOff) (n := 16) h (by decide) hk) (by decide)
  refine ⟨i₄, a₄, ?_, ?_, b₄, fun i hi => ?_, ?_⟩
  · exact ((p₁.fw.trans (fw_sub s₀ st₂.frame (by decide))).trans (fw_sub s₀ st₃.frame (by decide))).trans
      (fw_sub s₀ st₄.frame (by decide))
  · rw [stateAt_frame st₄.frame (st_disj s₀ (by decide) (by decide)),
      stateAt_frame st₃.frame (st_disj s₀ (by decide) (by decide)),
      stateAt_frame st₂.frame (st_disj s₀ (by decide) (by decide)), p₁.st]
  · rw [hz st₄.frame (by decide) (by decide) i hi, z₃ i hi]
  · rw [hl st₄.frame (by decide) (by decide), hl st₃.frame (by decide) (by decide),
      hl st₂.frame (by decide) (by decide), p₁.lens]


/-! ## After the encryption -/

theorem crypt_sub (s₀ : State) :
    ∀ r ∈ [sub s₀ 0 64, dR s₀, sub s₀ 64 320], ∃ r' ∈ [wR s₀, dR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨wR s₀, by simp, sub_work s₀ (by decide)⟩
  · exact ⟨dR s₀, by simp, fun _ h => h⟩
  · exact ⟨wR s₀, by simp, sub_work s₀ (by decide)⟩

/-- The parts of the context from the Poly1305 state on are apart from what
`crypt` writes. -/
theorem crypt_disj {s₀ : State} (hp : APre e s₀) {k n : Nat} (hk : 384 ≤ k) (hn : k + n ≤ 608) :
    ∀ r ∈ [sub s₀ 0 64, dR s₀, sub s₀ 64 320], (sub s₀ k n).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (.inr (by omega)) hn (by decide)
  · exact (APre.w_sub (s₀ := s₀) hp.d_w hn).symm
  · exact sub_disj s₀ (.inr (by omega)) hn (by decide)

/-- The data is apart from the working space. -/
theorem data_eq {s₀ : State} (hp : APre e s₀) {m : Mem} (hf : Frame [wR s₀] s₀.mem m) :
    bytesAt m (dp s₀) (L s₀) = D s₀ :=
  bytesAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.d_w)
    (Nat.le_of_lt (fit_d' s₀))

theorem length_encrypt (key nonce m : List Byte) :
    (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

theorem macData_eq (a c : List Byte) :
    Spec.ChaCha20Poly1305.macData a c =
      a ++ pad16 a ++ (c ++ pad16 c) ++ (leBytes 8 a.length ++ leBytes 8 c.length) := by
  simp [Spec.ChaCha20Poly1305.macData, List.append_assoc]

/-! ## Seal -/

theorem seal_correct {s₀ : State} (hp : APre true s₀) :
    WP isa Impl.ChaCha20Poly1305.RISCV64.«seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealRISCV64.post s₀ s' := by
  unfold «seal»
  refine head_ok hp fun s₄ h₄ => ?_
  refine WP.seq (WP.mono (crypt_ok hp h₄.inv h₄.a0 h₄.st) fun s₅ ⟨st₅, a₅, c₅⟩ => ?_)
  rw [data_eq hp h₄.fw] at c₅
  have i₅ : Inv s₀ s₅ := h₄.inv.step st₅ (crypt_sub s₀) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.d_w (by decide)).symm
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
  have B₅ := Buffered.frame st₅.frame (crypt_disj hp (k := polyOff) (n := 128) (by decide) (by decide)) h₄.buf
  have z₅ : ∀ i < 16, s₅.mem (off (cx s₀) (zeroOff + i)) = 0 := fun i hi => by
    rw [byte_frame st₅.frame (crypt_disj hp (k := zeroOff) (n := 16) (by decide) (by decide)) (by decide) hi,
      h₄.zero i hi]
  have l₅ : bytesAt s₅.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame st₅.frame (crypt_disj hp (k := lenOff) (n := 16) (by decide) (by decide)) (by decide),
      h₄.lens]
  have hOw : Covers [sub s₀ polyOff 128, tR s₀] s₀.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + polyOff, cx_off s₀ _, by
        show pad (wk s₀) + polyOff + 128 ≤ 616; simp only [polyOff]; omega⟩
    · exact ⟨tR s₀, hp.t_wr, 0, (BitVec.add_zero _).symm, by simp⟩
  refine WP.seq (WP.mono (macData_ok hp i₅ a₅ B₅ (length_pad16 _) z₅ l₅ (out := mov .a2 .s11) (O := tp s₀)
    (fun s i _ Q k => wp_mv fun s' u => WP.block_nil (k s' (by rw [i.regs.s11] at u; exact u)))
    (APre.w_sub (s₀ := s₀) hp.t_w (k := polyOff) (n := 128) (by decide)).symm hOw)
    fun s₆ ⟨st₆, a₆, t₆⟩ => ?_)
  refine wp_subi (imm := polyOff) (by decide) fun s₇ u₇ => ?_
  have hsv : Saved s₀ s₇.mem := by
    rw [u₇.mem]
    refine i₅.saved.frame st₆.frame fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.t_w (by decide)).symm
  refine WP.mono (restore_ok hp (by rw [u₇.gpr, a₆, ps, BitVec.add_sub_cancel]) hsv
    (by rw [u₇.rd, st₆.rd, i₅.rd]) (by rw [u₇.wr, st₆.wr, i₅.wr])) fun s' ⟨hr, hk, hm, hsp⟩ => ⟨?_, ?_⟩
  · exact abi_of i₅ hr (fun r hr' => by
      rw [hk r (by revert r; decide), u₇.other r (by revert r; decide), st₆.cs r (by revert r; decide)])
      (by rw [hsp, u₇.sp, st₆.sp, i₅.sp])
  · have d₆ : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s₅.mem (dp s₀) (L s₀) :=
      bytesAt_frame st₆.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact APre.w_sub (s₀ := s₀) hp.d_w (by decide)
        · exact hp.d_t) (Nat.le_of_lt (fit_d' s₀))
    show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
      (bytesAt s'.mem (dp s₀) (L s₀), bytesAt s'.mem (tp s₀) 16)
    rw [hm, u₇.mem, d₆, t₆, c₅, Spec.ChaCha20Poly1305.encrypt, macData_eq, length_encrypt,
      Proof.Poly1305.length_bytesAt, Proof.Poly1305.length_bytesAt]


/-! ## Comparing the tags -/

theorem or_zero_iff (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor <;> (apply BitVec.eq_of_getLsbD_eq; intro i hi
                     have := congrArg (fun z => z.getLsbD i) h
                     simp at this
                     simp [this])
  · rintro ⟨rfl, rfl⟩; rfl

theorem xor_zero_iff (x y : BitVec 64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h; have := congrArg (· ^^^ y) h; simpa [BitVec.xor_assoc] using this
  · rintro rfl; exact BitVec.xor_self

theorem lt_one_iff (x : BitVec 64) : x < BitVec.ofNat 64 1 ↔ x = 0 := by
  rw [BitVec.lt_def]
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; simp at h ⊢; omega
  · rintro rfl; decide

theorem setWidth_byte_inj (x y : Byte) : x.setWidth 64 = y.setWidth 64 ↔ x = y := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; rw [h]

theorem bytesAt_eq_iff (m : Mem) (p q : Addr) (n : Nat) :
    bytesAt m p n = bytesAt m q n ↔ ∀ i < n, m (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  constructor
  · intro h i hi
    have := congrArg (·.getD i 0) h
    exact (Proof.ChaCha20.bytesAt_getD m p hi).symm.trans (this.trans (Proof.ChaCha20.bytesAt_getD m q hi))
  · intro h
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- After the first `k` bytes compared. -/
structure CI (s₀ s s₂ : State) (k : Nat) (s' : State) : Prop where
  t0 : s'.gpr .t0 = cx s₀
  gpr : ∀ r, r ∉ [.t1, .t2, .t3] → s'.gpr r = s₂.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s₂.rd
  wr : s'.wr = s₂.wr
  sp : s'.sp = s₂.sp
  eq : s'.gpr .t1 = 0 ↔ ∀ i < k, s.mem (off (cx s₀) (tagOff + i)) = s.mem (tp s₀ + BitVec.ofNat 64 i)

theorem compare_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .t1 = (if bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16 then 1 else 0) →
      s'.gpr .t0 = cx s₀ → (∀ r, r ∉ [.t0, .t1, .t2, .t3] → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.ChaCha20Poly1305.RISCV64.compare ++ rest)) s Q := by
  unfold Impl.ChaCha20Poly1305.RISCV64.compare
  rw [List.append_assoc, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subi (imm := polyOff) (by decide) fun s₁ u₁ => wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  have t0₂ : s₂.gpr .t0 = cx s₀ := by rw [u₂.other _ (by decide), u₁.gpr, ha, ps, BitVec.add_sub_cancel]
  have s11₂ : s₂.gpr .s11 = tp s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s11]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, h.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (CI s₀ s s₂) (fun j x hj hx => ?_) 16 (Nat.le_refl _) s₂
    ⟨t0₂, fun _ _ => rfl, by rw [u₂.mem, u₁.mem], rfl, rfl, rfl,
      by rw [u₂.gpr]; exact ⟨fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩) fun s₃ h₃ => ?_
  · refine wp_lbu (a := off (cx s₀) (tagOff + j)) (by simp only [tagOff]; omega) (by rw [hx.t0])
      (by rw [hx.rd, hx.wr, rd₂, wr₂]; exact hp.in_w' (by simp only [tagOff]; omega)) fun y₁ v₁ => ?_
    refine wp_lbu (a := tp s₀ + BitVec.ofNat 64 j) (by omega)
      (by rw [v₁.other _ (by decide), hx.gpr _ (by decide), s11₂])
      (by rw [v₁.rd, v₁.wr, hx.rd, hx.wr, rd₂, wr₂]
          exact ⟨tR s₀, List.mem_append_left _ hp.t_rd, Offset.contains_base _ (by omega) (by omega)⟩)
      fun y₂ v₂ => wp_xor fun y₃ v₃ => wp_or fun y₄ v₄ => WP.block_nil ?_
    have o : ∀ r, r ∉ [.t1, .t2, .t3] → y₄.gpr r = x.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [v₄.other r hr.1, v₃.other r hr.2.1, v₂.other r hr.2.2, v₁.other r hr.2.1]
    refine ⟨by rw [o _ (by decide), hx.t0], fun r hr => by rw [o r hr, hx.gpr r hr],
      by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, hx.mem], by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hx.rd],
      by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hx.wr], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hx.sp], ?_⟩
    rw [v₄.gpr, v₃.gpr, v₃.other _ (by decide), v₂.gpr, v₂.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      v₁.other _ (by decide), v₁.mem, hx.mem, or_zero_iff, xor_zero_iff, setWidth_byte_inj, hx.eq]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h₁ i hi
      · exact h₂
    · intro h'; exact ⟨fun i hi => h' i (by omega), h' j (by omega)⟩
  refine wp_li (imm := 1) (by decide) fun s₄ u₄ => wp_sltu fun s₅ u₅ => k s₅ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have e : s₄.gpr .t1 < s₄.gpr .t2 ↔ bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16 := by
      rw [u₄.gpr, u₄.other _ (by decide), lt_one_iff, h₃.eq, bytesAt_eq_iff]
      exact forall_congr' fun i => imp_congr_right fun _ => by rw [Offset.add_add]
    rw [u₅.gpr]
    by_cases hc : bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16
    · simp only [eq_true (e.mpr hc), eq_true hc, ↓reduceIte]
    · simp only [eq_false (fun h' => hc (e.mp h')), eq_false hc, ↓reduceIte]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), h₃.t0]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other r hr.2.1, u₄.other r hr.2.2.1, h₃.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]),
      u₂.other r hr.2.1, u₁.other r hr.1]
  · rw [u₅.mem, u₄.mem, h₃.mem]
  · rw [u₅.rd, u₄.rd, h₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, h₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, h₃.sp, u₂.sp, u₁.sp]


/-! ## Open -/

theorem open_correct {s₀ : State} (hp : APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.RISCV64.«open» s₀ fun s' => abiPreserved s₀ s' ∧ openRISCV64.post s₀ s' := by
  unfold «open»
  refine head_ok hp fun s₄ h₄ => ?_
  have hOw : Covers [sub s₀ polyOff 128, sub s₀ tagOff 16] s₀.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + polyOff, cx_off s₀ _, by
        show pad (wk s₀) + polyOff + 128 ≤ 616; simp only [polyOff]; omega⟩
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + tagOff, cx_off s₀ _, by
        show pad (wk s₀) + tagOff + 16 ≤ 616; simp only [tagOff]; omega⟩
  have hO : ps s₀ + BitVec.ofNat 64 (tagOff - polyOff) = off (cx s₀) tagOff := (ps_add _ _).trans rfl
  refine WP.seq (WP.mono (macData_ok hp h₄.inv h₄.a0 h₄.buf (length_pad16 _) h₄.zero h₄.lens
    (out := .addi .a2 .a0 (tagOff - polyOff)) (O := off (cx s₀) tagOff)
    (fun s _ ha Q k => wp_addi (imm := tagOff - polyOff) (by decide) fun s' u =>
      WP.block_nil (k s' (by rw [ha, hO] at u; exact u)))
    (sub_disj s₀ (.inl (by decide)) (by decide) (by decide)) hOw) fun s₅ ⟨st₅, a₅, t₅⟩ => ?_)
  have i₅ := h₄.inv.step2 st₅ (by decide) (by decide)
  rw [data_eq hp h₄.fw] at t₅
  have f₅ : Frame [wR s₀] s₀.mem s₅.mem := h₄.fw.trans (st₅.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, sub_work s₀ (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, sub_work s₀ (by decide)⟩)
  have hst₅ : stateAt s₅.mem (cx s₀) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame st₅.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [st_sub]; exact sub_disj s₀ (.inl (by decide)) (by decide) (by decide)
      · rw [st_sub]; exact sub_disj s₀ (.inl (by decide)) (by decide) (by decide), h₄.st]
  refine WP.seq (WP.mono (crypt_ok hp i₅ a₅ hst₅) fun s₆ ⟨st₆, a₆, c₆⟩ => ?_)
  rw [data_eq hp f₅] at c₆
  have i₆ : Inv s₀ s₆ := i₅.step st₆ (crypt_sub s₀) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.d_w (by decide)).symm
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
  have t₆ : bytesAt s₆.mem (off (cx s₀) tagOff) 16 =
      mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) := by
    rw [bytesAt_frame st₆.frame (crypt_disj hp (k := tagOff) (n := 16) (by decide) (by decide)) (by decide), t₅,
      macData_eq, Proof.Poly1305.length_bytesAt, Proof.Poly1305.length_bytesAt]
  refine compare_ok hp i₆ a₆ fun s₇ t1₇ t0₇ g₇ m₇ rd₇ wr₇ sp₇ => ?_
  show WP isa (.block (restore ++ [mov .a0 .t1])) s₇ _
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hp t0₇ (by rw [m₇]; exact i₆.saved) (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr]))
    fun s₈ ⟨hr, hk, hm, hsp⟩ => ?_
  refine wp_mv fun s₉ u₉ => WP.block_nil ⟨?_, ?_⟩
  · refine abi_of i₆ (fun r hr' => by rw [u₉.other r (by revert r; decide), hr r hr'])
      (fun r hr' => by
        rw [u₉.other r (by revert r; decide), hk r (by revert r; decide), g₇ r (by revert r; decide)])
      (by rw [u₉.sp, hsp, sp₇, i₆.sp])
  · have a0₉ : s₉.gpr .a0 = if mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0 := by
      rw [u₉.gpr, hk _ (by decide), t1₇, t₆, tag_eq hp i₆]
    have d₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
      rw [u₉.mem, hm, m₇, c₆]
    show match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
      | some pt => s₉.gpr .a0 = 1 ∧ bytesAt s₉.mem (dp s₀) (L s₀) = pt
      | none => s₉.gpr .a0 = 0
    rw [a0₉]
    split
    next pt hpt =>
      obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
      exact ⟨by simp only [hmac, ↓reduceIte], d₉⟩
    next hn => simp only [decrypt_eq_none hn, ↓reduceIte]


/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data): `key` at `0x1000`, `nonce` at `0x1100`, `aad` at `0x2000`, `data` at 0,
`tag` at `0x3000` and `work` at `0x4000`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x1100 | .a2 => 0x2000 | .a6 => 0x3000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 616⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩, ⟨0x4000, 616⟩] }

theorem seal_ok (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.RISCV64.«seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_correct (APre.of s hs)

theorem open_ok (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.RISCV64.«open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_correct (APre.of s hs)

theorem seal_verified :
    Verified RISCV64.target Impl.ChaCha20Poly1305.RISCV64.«seal» (sealScratchContract RISCV64.abi 77) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
      Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.ChaCha20Poly1305.RISCV64.sealSat]
      using Proof.ChaCha20Poly1305.RISCV64.sealSat)

/-- The postconditions match on `decrypt`; the result is the low word of `a0`. -/
theorem open_verified :
    Verified RISCV64.target Impl.ChaCha20Poly1305.RISCV64.«open» (openScratchContract RISCV64.abi 77) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, RISCV64.abi, RISCV64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openRISCV64] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨by rw [h.1]; rfl, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => rw [h]; rfl
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
          [Proof.ChaCha20Poly1305.RISCV64.openSat, Proof.ChaCha20Poly1305.RISCV64.sealSat]
          using Proof.ChaCha20Poly1305.RISCV64.openSat }

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, RISCV64.abi, RISCV64.argRegs]
    [sealFrameSat, sealSat]
    using sealFrameSat

/-- `seal` with its working space in a frame of 624 bytes on the stack, wiped
after the code. -/
theorem seal_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 77 Impl.ChaCha20Poly1305.RISCV64.«seal»)
      (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 77) (post := Spec.ChaCha20Poly1305.sealPost RISCV64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 624) (words := 77) seal_verified (by decide) (by decide) (by decide)
    (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract RISCV64.abi 624).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, RISCV64.abi, RISCV64.argRegs]
    [openFrameSat, sealSat]
    using openFrameSat

/-- `open` with its working space in a frame of 624 bytes on the stack, wiped
after the code. -/
theorem open_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 77 Impl.ChaCha20Poly1305.RISCV64.«open»)
      (Spec.ChaCha20Poly1305.openContract RISCV64.abi 624) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 77) (post := Spec.ChaCha20Poly1305.openPost RISCV64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 624) (words := 77) open_verified (by decide) (by decide) (by decide)
    (openPost_out _) openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.RISCV64
