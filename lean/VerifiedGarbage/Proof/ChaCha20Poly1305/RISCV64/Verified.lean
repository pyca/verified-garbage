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
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgsWipe
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.RelCT

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
    (hd : ∀ r ∈ rs, (sub s₀ k n).Disjoint r) (hn : k + n ≤ 616) {i : Nat} (hi : i < n) :
    m' (off (cx s₀) (k + i)) = m (off (cx s₀) (k + i)) := by
  have := hf.bytes (R := sub s₀ k n) hd (by show n ≤ 2 ^ 64; omega) hi
  rwa [Offset.add_add] at this

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.a_w
    · exact hp.a_o) (Nat.le_of_lt (s₀.gpr .a3).isLt)

/-- The received tag is unchanged. -/
theorem tag_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (tp s₀) 16 = T0 s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.t_w
    · exact hp.o_t.symm) (by decide)

/-! ## Restoring the registers -/

/-- The registers `restore` loads. -/
abbrev restored : List Reg := [.s7, .s8, .s9, .s10, .s11, .ra, .s6]

theorem restore_ok {s₀ : State} (hp : APre e s₀) {s : State} (ht : s.gpr .t0 = cx s₀) (hs : Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ restored, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ restored → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  have hin : ∀ d, d + 8 ≤ 56 → InRegions (s.rd ++ s.wr) (off (cx s₀) (savOff + d)) 8 := fun d hd => by
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
    fun s₆ u₆ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 48)) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), ht]) (hal 48 (by decide))
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 48 (by decide))
    fun s₇ u₇ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, m₅]
  refine ⟨fun r hr => ?_, fun r hr => ?_, by rw [u₇.mem, m₆], by
    rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs.s7]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, hs.s8]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.mem, u₁.mem, hs.s9]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
        u₁.mem, hs.s10]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.s11]
    · rw [u₇.other _ (by decide), u₆.gpr, m₅, hs.ra]
    · rw [u₇.gpr, m₆, hs.s6]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h8, h9, h10, h11, hra, h6⟩ := hr
    rw [u₇.other r h6, u₆.other r hra, u₅.other r h11, u₄.other r h10, u₃.other r h9, u₂.other r h8,
      u₁.other r h7]

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

theorem st_disj (s₀ : State) {k n : Nat} (h : 64 ≤ k) (hk : k + n ≤ 616) :
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
      k + n ≤ 616 → ∀ i < 16, m' (off (cx s₀) (zeroOff + i)) = m (off (cx s₀) (zeroOff + i)) :=
    fun hf h hk i hi => byte_sub s₀ hf (by omega) hk (by simp only [zeroOff]; omega)
  have z₃ : ∀ i < 16, s₃.mem (off (cx s₀) (zeroOff + i)) = 0 := fun i hi => by
    rw [hz st₃.frame (by decide) (by decide) i hi, hz st₂.frame (by decide) (by decide) i hi, p₁.zero i hi]
  have b₃ : Buffered s₃.mem (ps s₀) (otk s₀) [] := ⟨r₃, rfl⟩
  refine WP.seq (WP.mono (macAad_ok hp i₃ a₃ b₃ z₃) fun s₄ ⟨st₄, a₄, b₄⟩ => k s₄ ?_)
  have i₄ := i₃.step1 st₄ (by decide)
  rw [aad_eq hp i₃] at b₄
  have hl : ∀ {m m' : Mem} {k n : Nat}, Frame [sub s₀ k n] m m' → (lenOff + 16 ≤ k ∨ k + n ≤ lenOff) →
      k + n ≤ 616 → bytesAt m' (off (cx s₀) lenOff) 16 = bytesAt m (off (cx s₀) lenOff) 16 :=
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
    ∀ r ∈ [sub s₀ 0 64, oR s₀, sub s₀ 64 320], ∃ r' ∈ [wR s₀, oR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨wR s₀, by simp, sub_work s₀ (by decide)⟩
  · exact ⟨oR s₀, by simp, fun _ h => h⟩
  · exact ⟨wR s₀, by simp, sub_work s₀ (by decide)⟩

/-- The parts of the context from the Poly1305 state on are apart from what
`crypt` writes. -/
theorem crypt_disj {s₀ : State} (hp : APre e s₀) {k n : Nat} (hk : 384 ≤ k) (hn : k + n ≤ 616) :
    ∀ r ∈ [sub s₀ 0 64, oR s₀, sub s₀ 64 320], (sub s₀ k n).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (.inr (by omega)) hn (by decide)
  · exact (APre.w_sub (s₀ := s₀) hp.o_w hn).symm
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
  rw [data_eq hp h₄.fw, show op s₀ = dp s₀ from hp.inPlace] at c₅
  have i₅ : Inv s₀ s₅ := h₄.inv.step st₅ (crypt_sub s₀) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.o_w (by decide)).symm
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
        show pad (wk s₀) + polyOff + 128 ≤ 624; simp only [polyOff]; omega⟩
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
        · have := hp.o_t
          simp only [oR, op, dp] at this ⊢
          rwa [show s₀.gpr .t6 = s₀.gpr .a4 from hp.inPlace] at this) (Nat.le_of_lt (fit_d' s₀))
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


/-! ## Zeroing the data -/

theorem ofNat_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat_ne_zero {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  exact Nat.ne_of_gt h this

/-- One step of `zeroData`'s loop: the byte at `op + j` zeroed, with `t1`
zero and `t2` at it. -/
theorem zeroStep_ok {s₀ : State} (hp : APre false s₀) {u : State} (hu : Inv s₀ u) {j : Nat}
    (hj : j < L s₀) (ht1 : u.gpr .t1 = 0) (ht2 : u.gpr .t2 = op s₀ + BitVec.ofNat 64 j)
    (hz : Proof.Zeroize.Prefix u.mem (op s₀) j) :
    WP isa (.block [.store .b .t1 .t2 0, .addi .t2 .t2 1, .addi .t3 .t3 (-1)]) u fun u' =>
      Inv s₀ u' ∧ u'.gpr .t1 = 0 ∧ u'.gpr .t2 = op s₀ + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .t3 = u.gpr .t3 - 1 ∧ (∀ r, r ≠ .t2 → r ≠ .t3 → u'.gpr r = u.gpr r) ∧
      Proof.Zeroize.Prefix u'.mem (op s₀) (j + 1) := by
  have hfit := hp.fit_o
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .a5).isLt
  have hc : (oR s₀).Contains (op s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_sb (off := 0) (a := op s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [ht2, BitVec.add_zero]) ⟨oR s₀, by rw [hu.wr]; exact hp.o_wr, hc⟩ fun u₁ m₁ => ?_
  refine wp_addi (imm := 1) (by decide) fun u₂ v₂ =>
    wp_subi (imm := 1) (by decide) fun u₃ v₃ => WP.block_nil ?_
  have st₁ : Step [oR s₀] u u₁ :=
    ⟨fun r _ => by rw [m₁.gpr], m₁.sp, m₁.rd, m₁.wr,
      by rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc⟩
  have st : Step [oR s₀] u u₃ := (st₁.trans (Step.upd _ v₂)).trans (Step.upd _ v₃)
  have o : ∀ r, r ≠ .t2 → r ≠ .t3 → u₃.gpr r = u.gpr r := fun r a b => by
    rw [v₃.other r b, v₂.other r a, m₁.gpr]
  refine ⟨hu.step st (fun r hr => ⟨oR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (APre.w_sub (s₀ := s₀) hp.o_w (by decide)).symm),
    by rw [o _ (by decide) (by decide), ht1], ?_, by rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr]; rfl, o, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, ht2, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [v₃.mem, v₂.mem, m₁.mem, ht1, show BitVec.setWidth 8 (0 : BitVec 64) = 0 by decide]
    exact Proof.Zeroize.prefix_writeW hz (by omega)

/-- `zeroData`, with `t1` zero: zeros at the destination, and only `t2` and `t3`
written. -/
theorem zeroData_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (ht1 : s.gpr .t1 = 0) :
    WP isa zeroData s fun s' => Inv s₀ s' ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0 ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .a5).isLt
  unfold zeroData
  refine WP.seq (wp_mv fun u₁ v₁ => wp_mv fun u₂ v₂ => WP.block_nil ?_)
  have t2₂ : u₂.gpr .t2 = op s₀ := by rw [v₂.other _ (by decide), v₁.gpr, h.regs.s6]
  have t3₂ : u₂.gpr .t3 = BitVec.ofNat 64 (L s₀) := by
    rw [v₂.gpr, v₁.other _ (by decide), h.regs.s10, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have i₂ : Inv s₀ u₂ := h.step ((Step.upd [] v₁).trans (Step.upd [] v₂)) (by simp) (by simp)
  have o₂ : ∀ r, r ≠ .t2 → r ≠ .t3 → u₂.gpr r = s.gpr r := fun r a b => by
    rw [v₂.other r b, v₁.other r a]
  by_cases hz : L s₀ = 0
  · refine WP.ite true (by simp only [VG.RISCV64.eval, t3₂, hz]; rfl) (fun _ => WP.block_nil ⟨i₂, ?_, o₂⟩)
      (by simp)
    rw [hz]; rfl
  · have hne := ofNat_ne_zero (n := L s₀) (by omega) hL
    refine WP.ite false (by show some (u₂.gpr .t3 == 0) = some false; rw [t3₂, beq_false_of_ne hne])
      (by simp) fun _ => ?_
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < L s₀ ∧ rem = L s₀ - j ∧ Inv s₀ u ∧ u.gpr .t1 = 0 ∧
      u.gpr .t2 = op s₀ + BitVec.ofNat 64 j ∧ u.gpr .t3 = BitVec.ofNat 64 (L s₀ - j) ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → u.gpr r = s.gpr r) ∧ Proof.Zeroize.Prefix u.mem (op s₀) j) ?_ (L s₀) u₂
      ⟨0, by omega, by omega, i₂, by rw [o₂ _ (by decide) (by decide), ht1],
        by rw [t2₂]; exact (BitVec.add_zero _).symm, by rw [t3₂, Nat.sub_zero], o₂,
        fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem u ⟨j, hj, hr, hu, h1, h2, h3, ho, hpz⟩
    refine WP.mono (zeroStep_ok hp hu hj h1 h2 hpz) fun u' ⟨i', t1', t2', t3', o', z'⟩ => ?_
    have t3'' : u'.gpr .t3 = BitVec.ofNat 64 (L s₀ - (j + 1)) := by
      rw [t3', h3, ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
    have o'' : ∀ r, r ≠ .t2 → r ≠ .t3 → u'.gpr r = s.gpr r := fun r a b => by rw [o' r a b, ho r a b]
    by_cases he : j + 1 = L s₀
    · left
      refine ⟨by simp only [VG.RISCV64.eval, t3'', he, Nat.sub_self]; rfl, i', ?_, o''⟩
      rw [he] at z'
      exact Proof.Zeroize.prefix_spec z'
    · right
      have hne := ofNat_ne_zero (n := L s₀ - (j + 1)) (by omega) (by omega)
      refine ⟨by show some (u'.gpr .t3 != 0) = some true; rw [t3'', bne, beq_false_of_ne hne]; rfl,
        L s₀ - (j + 1), by omega, j + 1, by omega, rfl, i', t1', t2', t3'', o'', z'⟩

/-! ## Open -/

/-- The epilogue, from the context in `t0`: our caller's registers restored,
and the result `t1` in `a0`. -/
theorem tail_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (ht : s.gpr .t0 = cx s₀) :
    WP isa (.block (restore ++ [mov .a0 .t1])) s fun s' =>
      abiPreserved s₀ s' ∧ s'.gpr .a0 = s.gpr .t1 ∧ s'.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hp ht h.saved h.rd h.wr) fun s₈ ⟨hr, hk, hm, hsp⟩ => ?_
  refine wp_mv fun s₉ u₉ => WP.block_nil ⟨?_, by rw [u₉.gpr, hk _ (by decide)], by rw [u₉.mem, hm]⟩
  exact abi_of h (fun r hr' => by rw [u₉.other r (by revert r; decide), hr r hr'])
    (fun r hr' => by rw [u₉.other r (by revert r; decide), hk r (by revert r; decide)])
    (by rw [u₉.sp, hsp, h.sp])

/-- Everything but the epilogue: `t1` is whether the tag is right, the
plaintext is at the destination, and the context is in `t0`. -/
theorem body_ok {s₀ : State} (hp : APre false s₀) :
    WP isa openBody s₀ fun s₇ => Inv s₀ s₇ ∧ s₇.gpr .t0 = cx s₀ ∧
      s₇.gpr .t1 = (if mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0) ∧
      bytesAt s₇.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  unfold openBody
  refine head_ok hp fun s₄ h₄ => ?_
  have hOw : Covers [sub s₀ polyOff 128, sub s₀ tagOff 16] s₀.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + polyOff, cx_off s₀ _, by
        show pad (wk s₀) + polyOff + 128 ≤ 624; simp only [polyOff]; omega⟩
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + tagOff, cx_off s₀ _, by
        show pad (wk s₀) + tagOff + 16 ≤ 624; simp only [tagOff]; omega⟩
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
    · exact ⟨_, List.mem_singleton_self _, sub_work s₀ (k := polyOff) (n := 128) (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, sub_work s₀ (k := tagOff) (n := 16) (by decide)⟩)
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
    · exact (APre.w_sub (s₀ := s₀) hp.o_w (by decide)).symm
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
  have t₆ : bytesAt s₆.mem (off (cx s₀) tagOff) 16 =
      mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) := by
    rw [bytesAt_frame st₆.frame (crypt_disj hp (k := tagOff) (n := 16) (by decide) (by decide)) (by decide), t₅,
      macData_eq, Proof.Poly1305.length_bytesAt, Proof.Poly1305.length_bytesAt]
  rw [show Impl.ChaCha20Poly1305.RISCV64.compare = Impl.ChaCha20Poly1305.RISCV64.compare ++ [] from
    (List.append_nil _).symm]
  refine compare_ok hp i₆ a₆ fun s₇ t1₇ t0₇ g₇ m₇ rd₇ wr₇ sp₇ => WP.block_nil ?_
  have i₇ : Inv s₀ s₇ := i₆.step (rs := [])
    ⟨fun r hr => g₇ r (by revert r; decide), sp₇, rd₇, wr₇, by rw [m₇]; exact Frame.refl _ _⟩
    (by simp) (by simp)
  have ok₇ : s₇.gpr .t1 =
      if mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0 := by
    rw [t1₇, t₆, tag_eq hp i₆]
  exact ⟨i₇, t0₇, ok₇, by rw [m₇, c₆]⟩

/-- What `open`'s body leaves, from the source to the destination: the
result in `a0`, and the plaintext or zeros at the destination. -/
def CorePost (s₀ s' : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
  | some pt => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (op s₀) (L s₀) = pt
  | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0

theorem open_correct {s₀ : State} (hp : APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.RISCV64.«open» s₀ fun s' => abiPreserved s₀ s' ∧ CorePost s₀ s' := by
  unfold «open»
  refine WP.seq (WP.mono (body_ok hp) fun s₇ ⟨i₇, t0₇, ok₇, d₇⟩ => ?_)
  show WP isa (.seq (.ite (.zero .t1) zeroData (.block [])) (.block (restore ++ [mov .a0 .t1]))) s₇ fun s' =>
    abiPreserved s₀ s' ∧ match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
      | some pt => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (op s₀) (L s₀) = pt
      | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0
  refine WP.seq ?_
  by_cases hc : mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀
  · simp only [hc, ↓reduceIte] at ok₇
    refine WP.ite false (by simp only [VG.RISCV64.eval, ok₇]; rfl) (by simp) fun _ => WP.block_nil ?_
    refine WP.mono (tail_ok hp i₇ t0₇) fun s₉ ⟨ha, a0₉, m₉⟩ => ⟨ha, ?_⟩
    split
    next pt hpt =>
      obtain ⟨-, rfl⟩ := decrypt_eq_some hpt
      exact ⟨by rw [a0₉, ok₇], by rw [m₉, d₇]⟩
    next hn => exact absurd hc (decrypt_eq_none hn)
  · simp only [hc, ↓reduceIte] at ok₇
    refine WP.ite true (by simp only [VG.RISCV64.eval, ok₇]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (zeroData_ok hp i₇ ok₇) fun s₈ ⟨i₈, z₈, o₈⟩ => ?_
    refine WP.mono (tail_ok hp i₈ (by rw [o₈ _ (by decide) (by decide), t0₇])) fun s₉ ⟨ha, a0₉, m₉⟩ => ⟨ha, ?_⟩
    split
    next pt hpt => exact absurd (decrypt_eq_some hpt).1 hc
    next hn => exact ⟨by rw [a0₉, o₈ _ (by decide) (by decide), ok₇], by rw [m₉, z₈]⟩


/-! ## Constant time

Two runs of `open`'s body from states with the same public data leak the
same (`open_rel`): `openBody` by the taint analysis; then both branch the
same way, as whether the tag is right is public; the zeroing and the
epilogue by the taint analysis, from the public data that `body_ok` and
`zeroData_ok` give them in both runs. Each entry then reaches that body
with the same public data in both runs. -/

/-- Both states satisfy `I`. -/
abbrev Both (I : State → Prop) : State → State → Prop := fun s₁ s₂ => I s₁ ∧ I s₂

theorem ct_seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : RelCT isa (Both I) c₁ fun _ _ => True)
    (w : ∀ s, I s → WP isa c₁ s J) (h₂ : RelCT isa (Both J) c₂ fun _ _ => True) :
    RelCT isa (Both I) (.seq c₁ c₂) fun _ _ => True :=
  ((h₁.wp fun s₁ s₂ h => ⟨w s₁ h.1, w s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2).seq h₂

theorem ct_taint {I : State → Prop} {c : Prog isa} (rs : List Reg) (v : Reg → BitVec 64) (sp : Addr)
    (hp : ∀ s, I s → s.sp = sp ∧ ∀ r ∈ rs, s.gpr r = v r) {h : VG.Taint.Hint VG.RISCV64.taint.T}
    (hc : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Both I) c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun _ _ hh => ⟨(hp _ hh.1).1.trans (hp _ hh.2).1.symm, fun r h' =>
      ((hp _ hh.1).2 r (Taint.mem_ofRegs.mp h')).trans ((hp _ hh.2).2 r (Taint.mem_ofRegs.mp h')).symm⟩) hc

theorem ok_iff (s₀ : State) :
    okRISCV64 s₀ = true ↔ mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ := by
  unfold okRISCV64
  constructor
  · intro h
    obtain ⟨pt, hpt⟩ := Option.isSome_iff_exists.mp h
    exact (decrypt_eq_some hpt).1
  · intro h
    cases hd : Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | none => exact absurd h (decrypt_eq_none hd)
    | some _ => rfl

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The registers the body reads as public on entry. -/
abbrev pubRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t6]

/-- What two runs of the body agree on: the public registers (`v`), the
stack pointer and whether the tag is right. -/
def Core (v : Reg → BitVec 64) (sp : Addr) (b : Bool) (s : State) : Prop :=
  APre false s ∧ (∀ r ∈ pubRegs, s.gpr r = v r) ∧ s.sp = sp ∧ okRISCV64 s = b

theorem open_rel (v : Reg → BitVec 64) (sp : Addr) (bo : Bool) :
    RelCT isa (Both (Core v sp bo)) Impl.ChaCha20Poly1305.RISCV64.«open» fun _ _ => True := by
  let c : Addr := v .a7 + BitVec.ofNat 64 (pad (v .a7))
  let b : BitVec 64 := if bo then 1 else 0
  let J : State → Prop := fun s => s.sp = sp ∧ s.gpr .t0 = c ∧ s.gpr .t1 = b ∧
    s.gpr .s6 = v .t6 ∧ s.gpr .s10 = v .a5 ∧ ∃ t₀, Core v sp bo t₀ ∧ Inv t₀ s
  let J' : State → Prop := fun s => s.sp = sp ∧ s.gpr .t0 = c
  unfold «open»
  refine ct_seq (J := J) ?_ ?_ ?_
  · obtain ⟨_, hc⟩ := openBody_taint
    exact ct_taint _ v sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
  · intro s ⟨hp, e, esp, eok⟩
    refine WP.mono (body_ok hp) fun s' ⟨i, t0, t1, _⟩ => ⟨by rw [i.sp, esp], ?_, ?_,
      by rw [i.regs.s6, e .t6 (by decide)], by rw [i.regs.s10, e .a5 (by decide)], s, ⟨hp, e, esp, eok⟩, i⟩
    · rw [t0]; show wk s + _ = _; simp only [wk, e .a7 (by decide), c]
    · rw [t1]; show _ = if bo = true then _ else _
      rw [← eok]; simp only [ok_iff]
  · refine ct_seq (J := J') ?_ ?_ ?_
    · refine RelCT.ite (fun _ _ h => by simp only [VG.RISCV64.eval, h.1.2.2.1, h.2.2.2.1]) ?_ ?_
      · obtain ⟨_, hc⟩ := zeroData_taint
        refine RelCT.mono (ct_taint (I := J) _ (fun r => match r with | .s6 => v .t6 | _ => v .a5)
          sp (fun s hs => ⟨hs.1, ?_⟩) hc)
          (fun _ _ h => h.1) fun _ _ h => h
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.2.2.2.1
        · exact hs.2.2.2.2.1
      · intro _ _ _ _ _ _ _ x₁ x₂
        cases x₁ with
        | block h₁ =>
          cases x₂ with
          | block h₂ =>
            simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
            exact ⟨h₁.2.symm.trans h₂.2, trivial⟩
    · rintro s ⟨esp, et0, et1, -, -, t₀, ⟨hp, -⟩, i⟩
      by_cases hb : bo = true
      · have : s.gpr .t1 = 1 := by rw [et1]; simp only [b, hb, ↓reduceIte]
        exact WP.ite (M := isa) (c := .zero .t1) false (by simp only [VG.RISCV64.eval, this]; rfl) (by simp)
          fun _ => WP.block_nil ⟨esp, et0⟩
      · have : s.gpr .t1 = 0 := by rw [et1]; simp only [b, hb, Bool.false_eq_true, ↓reduceIte]
        exact WP.ite (M := isa) (c := .zero .t1) true (by simp only [VG.RISCV64.eval, this]; rfl)
          (fun _ => WP.mono (zeroData_ok hp i this) fun s' ⟨i', _, o'⟩ =>
            ⟨by rw [i'.sp, ← i.sp, esp], by rw [o' _ (by decide) (by decide), et0]⟩) (by simp)
    · obtain ⟨_, hc⟩ := tail_taint
      exact ct_taint _ (fun _ => c) sp (fun s hs => ⟨hs.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.2⟩) hc

/-! ## In place -/

/-- After `mv t6, a4`, from the precondition of `seal` or `open`: the
destination is the source. -/
theorem apre_inPlace {enc : Bool} {s s₁ : State} (hs : preRISCV64 enc s)
    (u : Steps.Upd s s₁ .t6 (s.gpr .a4)) : APre enc s₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hs
  have g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s₁.gpr r = s.gpr r := fun r hr =>
    u.other r (by revert r; decide)
  have g6 : s₁.gpr .t6 = s.gpr .a4 := u.gpr
  have e : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s₁.gpr r = s.gpr r := g
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := e
  have rd : s₁.rd = s.rd := u.rd
  have wr : s₁.wr = s.wr := u.wr
  refine {
    k_rd := by simp only [kR, kp, e0, rd, h1]; cases enc <;> simp
    n_rd := by simp only [nR, np, e1, rd, h1]; cases enc <;> simp
    a_rd := by simp only [aR, ad, AL, e2, e3, rd, h1]; cases enc <;> simp
    d_in := by simp only [dR, dp, L, e4, e5, rd, wr, h1, h2]; cases enc <;> simp
    o_wr := by simp only [oR, op, L, g6, e5, wr, h2]; cases enc <;> simp
    w_wr := by simp only [wR, wk, e7, wr, h2]; cases enc <;> simp
    t_in := by cases enc <;> simp only [tR, tp, e6, rd, wr, h1, h2, ↓reduceIte] <;> simp
    k_w := ?_, n_w := ?_, a_w := ?_, d_w := ?_, t_w := ?_,
    k_o := ?_, n_o := ?_, a_o := ?_, o_t := ?_, o_w := ?_, alias := ?_, enc_t := ?_,
    fit_k := ?_, fit_n := ?_, fit_a := ?_, fit_d := ?_, fit_o := ?_, fit_t := ?_, fit_w := ?_ } <;>
  simp only [kR, kp, nR, np, aR, ad, AL, dR, dp, L, tR, tp, wR, wk, oR, op, e0, e1, e2, e3, e4, e5, e6, e7,
    g6] <;>
  first
    | exact .inl rfl
    | with_reducible assumption
    | (cases enc <;> simp_all)

theorem abi_inPlace {s s₁ s' : State} (u : Steps.Upd s s₁ .t6 (s.gpr .a4)) (h : abiPreserved s₁ s') :
    abiPreserved s s' :=
  ⟨fun r hr => by rw [h.1 r hr, u.other r (by revert r; decide)], by rw [h.2.1, u.sp],
    by rw [h.2.2, u.other _ (by decide)]⟩

theorem inPlace_ok {enc : Bool} {c : Prog isa} {s : State} (hs : preRISCV64 enc s) {Q : State → Prop}
    (k : ∀ s₁, Steps.Upd s s₁ .t6 (s.gpr .a4) → APre enc s₁ → WP isa c s₁ Q) :
    WP isa (Impl.ChaCha20Poly1305.RISCV64.inPlace c) s Q :=
  WP.seq (wp_mv fun s₁ u => WP.block_nil (k s₁ u (apre_inPlace hs u)))

theorem ok_inPlace {s s₁ : State} (u : Steps.Upd s s₁ .t6 (s.gpr .a4)) : okRISCV64 s₁ = okRISCV64 s := by
  simp only [okRISCV64, u.mem, u.other .a0 (by decide), u.other .a1 (by decide), u.other .a2 (by decide),
    u.other .a3 (by decide), u.other .a4 (by decide), u.other .a5 (by decide), u.other .a6 (by decide)]

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub
    (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open») := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩, ql⟩ := hq
  have qok : okRISCV64 σ₁ = okRISCV64 σ₂ := leak_bool ql
  let v : Reg → BitVec 64 := fun r => if r = .t6 then σ₁.gpr .a4 else σ₁.gpr r
  let I₀ : State → Prop := fun s => preRISCV64 false s ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7],
    s.gpr r = σ₁.gpr r) ∧ s.sp = σ₁.sp ∧ okRISCV64 s = okRISCV64 σ₁
  have hc : RelCT isa (Both I₀)
      (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open») fun _ _ => True := by
    unfold Impl.ChaCha20Poly1305.RISCV64.inPlace
    refine ct_seq (J := Core v σ₁.sp (okRISCV64 σ₁)) ?_ ?_ (open_rel v σ₁.sp _)
    · obtain ⟨_, hc⟩ := inPlace_taint
      exact ct_taint _ σ₁.gpr σ₁.sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
    · intro s ⟨hpre, e, esp, eok⟩
      refine wp_mv fun s₁ u => WP.block_nil ⟨apre_inPlace hpre u, fun r hr => ?_, by rw [u.sp, esp],
        by rw [ok_inPlace u, eok]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .a0 = σ₁.gpr .a0; rw [u.other _ (by decide)]; exact e .a0 (by simp)
      · show s₁.gpr .a1 = σ₁.gpr .a1; rw [u.other _ (by decide)]; exact e .a1 (by simp)
      · show s₁.gpr .a2 = σ₁.gpr .a2; rw [u.other _ (by decide)]; exact e .a2 (by simp)
      · show s₁.gpr .a3 = σ₁.gpr .a3; rw [u.other _ (by decide)]; exact e .a3 (by simp)
      · show s₁.gpr .a4 = σ₁.gpr .a4; rw [u.other _ (by decide)]; exact e .a4 (by simp)
      · show s₁.gpr .a5 = σ₁.gpr .a5; rw [u.other _ (by decide)]; exact e .a5 (by simp)
      · show s₁.gpr .a6 = σ₁.gpr .a6; rw [u.other _ (by decide)]; exact e .a6 (by simp)
      · show s₁.gpr .a7 = σ₁.gpr .a7; rw [u.other _ (by decide)]; exact e .a7 (by simp)
      · show s₁.gpr .t6 = σ₁.gpr .a4; rw [u.gpr]; exact e .a4 (by simp)
  exact (hc _ _ _ _ _ _ ⟨⟨h₁, fun r _ => rfl, rfl, rfl⟩,
    ⟨h₂, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0.symm, q1.symm, q2.symm, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm],
      qsp.symm, qok.symm⟩⟩ e₁ e₂).1

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
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 624⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩, ⟨0x4000, 624⟩] }

theorem seal_ok (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal») s t s' ∧
      abiPreserved s s' ∧ sealRISCV64.post s s' :=
  inPlace_ok hs fun s₁ u hp => WP.mono (seal_correct hp) fun s' ⟨ha, hpost⟩ => ⟨abi_inPlace u ha, by
    simpa only [sealRISCV64, u.mem, u.other .a0 (by decide), u.other .a1 (by decide), u.other .a2 (by decide),
      u.other .a3 (by decide), u.other .a4 (by decide), u.other .a5 (by decide), u.other .a6 (by decide)]
      using hpost⟩

theorem open_ok (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open») s t s' ∧
      abiPreserved s s' ∧ openRISCV64.post s s' :=
  inPlace_ok hs fun s₁ u hp => WP.mono (open_correct hp) fun s' ⟨ha, hpost⟩ => ⟨abi_inPlace u ha, by
    have ed : Spec.ChaCha20Poly1305.decrypt (K s₁) (N s₁) (A s₁) (D s₁) (T0 s₁) =
        Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
          (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
          (bytesAt s.mem (s.gpr .a6) 16) := by
      simp only [K, N, A, D, T0, kp, np, ad, AL, dp, L, tp, u.mem, u.other .a0 (by decide),
        u.other .a1 (by decide), u.other .a2 (by decide), u.other .a3 (by decide), u.other .a4 (by decide),
        u.other .a5 (by decide), u.other .a6 (by decide)]
    have eo : op s₁ = s.gpr .a4 := u.gpr
    have eL : L s₁ = (s.gpr .a5).toNat := by simp only [L, u.other .a5 (by decide)]
    unfold CorePost at hpost
    rw [ed, eo, eL] at hpost
    simp only [openRISCV64]
    split at hpost <;> rename_i heq <;> simp only [heq] <;> exact hpost⟩

theorem seal_verified :
    Verified RISCV64.target (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
      (sealScratchContract RISCV64.abi 78) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
      Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.ChaCha20Poly1305.RISCV64.sealSat]
      using Proof.ChaCha20Poly1305.RISCV64.sealSat)

/-- The postconditions match on `decrypt`; the result is the low word of `a0`. -/
theorem open_verified :
    Verified RISCV64.target (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
      (openZeroScratchContract RISCV64.abi 78) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openRISCV64,
          Proof.ChaCha20Poly1305.openLeakRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, RISCV64.abi, RISCV64.argRegs]
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
          next _ e₂ => exact ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openRISCV64,
          Proof.ChaCha20Poly1305.openLeakRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openRISCV64,
          Proof.ChaCha20Poly1305.openLeakRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
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
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
        (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»))
      (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 78) (post := Spec.ChaCha20Poly1305.sealPost RISCV64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 624) (words := 78) seal_verified (by decide) (by decide) (by decide)
    (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract RISCV64.abi 624).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, RISCV64.abi, RISCV64.argRegs]
    [openFrameSat, sealSat]
    using openFrameSat

/-- `open` with its working space in a frame of 624 bytes on the stack, wiped
after the code. -/
theorem open_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
        (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»))
      (Spec.ChaCha20Poly1305.openZeroContract RISCV64.abi 624) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 78) (post := Spec.ChaCha20Poly1305.openZeroPost RISCV64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openLeak RISCV64.abi.ptrBits))
    (bytes := 624) (words := 78) open_verified (by decide) (by decide) (by decide)
    (openZeroPost_out _) openFrameSat_pre

/-! ## Out of place

`vg_chacha20_poly1305_open_to` is `open`'s body after `toEntry`: `dst` into
`t6`, and `tag` and `work` from the stack into `a6` and `a7`, where the body
expects them. -/

/-- After `toEntry`. -/
structure ToEntered (s s₄ : State) : Prop where
  gpr : ∀ r, r ≠ .t6 → r ≠ .t0 → r ≠ .a6 → r ≠ .a7 → s₄.gpr r = s.gpr r
  t6 : s₄.gpr .t6 = s.gpr .a6
  a6 : s₄.gpr .a6 = stackArg s 0
  a7 : s₄.gpr .a7 = stackArg s 1
  mem : s₄.mem = s.mem
  sp : s₄.sp = s.sp
  rd : s₄.rd = s.rd
  wr : s₄.wr = s.wr

theorem toEntry_ok {s : State} (hs : openToPreRISCV64 s) : WP isa (.block toEntry) s (ToEntered s) := by
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfa, hal, _, _⟩ := hs
  have hin : ∀ j, j < 2 → InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := fun j hj => by
    refine ⟨toArgs s, by rw [hrd]; simp, ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 16⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * j)) 8
    exact Offset.contains _ (by omega) (by omega) (by simp only [stackArgAddr] at hfa; omega)
  have hal8 : ∀ j, (stackArgAddr s j).toNat % 8 = 0 := fun j =>
    Spill.al8 (by omega) (by omega)
  unfold toEntry
  refine wp_mv fun s₁ u₁ => wp_addSp (imm := 0) (by decide) fun s₂ u₂ => ?_
  have p₂ : s₂.gpr .t0 = s.sp := by rw [u₂.gpr, u₁.sp, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by rw [p₂]; rfl) (hal8 0)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by decide) (by rw [u₃.other _ (by decide), p₂]; rfl) (hal8 1)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 1 (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact ⟨fun r h6 h0 ha6 ha7 => by rw [u₄.other r ha7, u₃.other r ha6, u₂.other r h0, u₁.other r h6],
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]; rfl,
    by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]; rfl, hm,
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩

theorem apre_openTo {s s₄ : State} (hs : openToPreRISCV64 s) (h : ToEntered s s₄) : APre false s₄ := by
  obtain ⟨h1, h2, dk, dn, da, ds, dt, dw, dg, wk', wn, wa, ws, wt, wg, f0, f1, f2, f4, f6, ft, fw, -, -, hl, -⟩ :=
    hs
  have e0 := h.gpr .a0 (by decide) (by decide) (by decide) (by decide)
  have e1 := h.gpr .a1 (by decide) (by decide) (by decide) (by decide)
  have e2 := h.gpr .a2 (by decide) (by decide) (by decide) (by decide)
  have e3 := h.gpr .a3 (by decide) (by decide) (by decide) (by decide)
  have e4 := h.gpr .a4 (by decide) (by decide) (by decide) (by decide)
  have e5 := h.gpr .a5 (by decide) (by decide) (by decide) (by decide)
  simp only [hl] at h1 h2 dk dn da ds dt dw dg f6
  refine {
    k_rd := ?_, n_rd := ?_, a_rd := ?_, d_in := ?_, o_wr := ?_, w_wr := ?_, t_in := ?_,
    k_w := ?_, n_w := ?_, a_w := ?_, d_w := ?_, t_w := ?_,
    k_o := ?_, n_o := ?_, a_o := ?_, o_t := ?_, o_w := ?_, enc_t := trivial,
    alias := by
      refine .inr ⟨rfl, ?_⟩
      simp only [dR, dp, L, oR, op, e4, e5, h.t6]
      exact ds.symm,
    fit_k := ?_, fit_n := ?_, fit_a := ?_, fit_d := ?_, fit_o := ?_, fit_t := ?_, fit_w := ?_ } <;>
  simp only [kR, kp, nR, np, aR, ad, AL, dR, dp, L, tR, tp, wR, wk, oR, op, e0, e1, e2, e3, e4, e5, h.t6,
    h.a6, h.a7, h.rd, h.wr, h1, h2, Bool.false_eq_true, ↓reduceIte] <;>
  first
    | with_reducible assumption
    | (apply Region.Disjoint.symm; with_reducible assumption)
    | simp
    | omega

theorem abi_openTo {s s₄ s' : State} (h : ToEntered s s₄) (ha : abiPreserved s₄ s') : abiPreserved s s' :=
  ⟨fun r hr => by
    rw [ha.1 r hr, h.gpr r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)], by rw [ha.2.1, h.sp],
    by rw [ha.2.2, h.gpr _ (by decide) (by decide) (by decide) (by decide)]⟩

theorem ok_openTo {s s₄ : State} (h : ToEntered s s₄) : okRISCV64 s₄ = (openToRes s).isSome := by
  simp only [okRISCV64, openToRes, h.mem, h.a6, h.gpr .a0 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a1 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a2 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a3 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a4 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a5 (by decide) (by decide) (by decide) (by decide)]

theorem openTo_ok (s : State) (hs : openToRISCV64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.RISCV64.openTo s t s' ∧ abiPreserved s s' ∧
      openToRISCV64.post s s' :=
  WP.seq (WP.mono (toEntry_ok hs) fun s₄ h₄ => WP.mono (open_correct (apre_openTo hs h₄))
    fun s' ⟨ha, hpost⟩ => ⟨abi_openTo h₄ ha, by
      have ed : Spec.ChaCha20Poly1305.decrypt (K s₄) (N s₄) (A s₄) (D s₄) (T0 s₄) = openToRes s := by
        simp only [K, N, A, D, T0, kp, np, ad, AL, dp, L, tp, openToRes, h₄.mem, h₄.a6,
          h₄.gpr .a0 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a1 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a2 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a3 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a4 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a5 (by decide) (by decide) (by decide) (by decide)]
      have eo : op s₄ = s.gpr .a6 := h₄.t6
      have eL : L s₄ = (s.gpr .a5).toNat := by
        simp only [L, h₄.gpr .a5 (by decide) (by decide) (by decide) (by decide)]
      unfold CorePost at hpost
      rw [ed, eo, eL] at hpost
      simp only [openToRISCV64]
      split at hpost <;> rename_i heq <;> simp only [heq] <;> exact hpost⟩)

theorem openTo_ct : ConstantTime isa openToRISCV64.pre openToRISCV64.pub Impl.ChaCha20Poly1305.RISCV64.openTo := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩, qa, ql⟩ := hq
  have qok : (openToRes σ₁).isSome = (openToRes σ₂).isSome := leak_bool ql
  let v : Reg → BitVec 64 := fun r =>
    if r = .t6 then σ₁.gpr .a6 else if r = .a6 then stackArg σ₁ 0 else if r = .a7 then stackArg σ₁ 1
    else σ₁.gpr r
  let I₀ : State → Prop := fun s => openToPreRISCV64 s ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7],
    s.gpr r = σ₁.gpr r) ∧ s.sp = σ₁.sp ∧ (∀ i < 2, stackArg s i = stackArg σ₁ i) ∧
    (openToRes s).isSome = (openToRes σ₁).isSome
  have hc : RelCT isa (Both I₀) Impl.ChaCha20Poly1305.RISCV64.openTo fun _ _ => True := by
    unfold Impl.ChaCha20Poly1305.RISCV64.openTo
    refine ct_seq (J := Core v σ₁.sp (openToRes σ₁).isSome) ?_ ?_ (open_rel v σ₁.sp _)
    · obtain ⟨_, hc⟩ := toEntry_taint
      exact ct_taint _ σ₁.gpr σ₁.sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
    · intro s ⟨hpre, e, esp, ea, eok⟩
      refine WP.mono (toEntry_ok hpre) fun s₄ h₄ => ⟨apre_openTo hpre h₄, fun r hr => ?_,
        by rw [h₄.sp, esp], by rw [ok_openTo h₄, eok]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have g : ∀ r, r ≠ .t6 → r ≠ .t0 → r ≠ .a6 → r ≠ .a7 → r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] →
          s₄.gpr r = σ₁.gpr r := fun r a b c d hm => (h₄.gpr r a b c d).trans (e r hm)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact g .a0 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a1 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a2 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a3 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a4 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a5 (by decide) (by decide) (by decide) (by decide) (by simp)
      · show s₄.gpr .a6 = stackArg σ₁ 0; rw [h₄.a6]; exact ea 0 (by decide)
      · show s₄.gpr .a7 = stackArg σ₁ 1; rw [h₄.a7]; exact ea 1 (by decide)
      · show s₄.gpr .t6 = σ₁.gpr .a6; rw [h₄.t6]; exact e .a6 (by simp)
  exact (hc _ _ _ _ _ _ ⟨⟨h₁, fun r _ => rfl, rfl, fun i _ => rfl, rfl⟩,
    ⟨h₂, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0.symm, q1.symm, q2.symm, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm],
      qsp.symm, fun i hi => (qa i hi).symm, qok.symm⟩⟩ e₁ e₂).1

/-- A state satisfying `open_to`'s precondition (with no additional data and
no data): `key`, `nonce` and `aad` as in `sealSat`, `src` at `0x5000`, `dst`
at 0, `tag` at `0x3000` and `work` at `0x4000`, both on the stack at `sp`. -/
def openToSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x1100 | .a2 => 0x2000 | .a4 => 0x5000 | _ => 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8001 then 0x30 else bif Nat.beq a.toNat 0x8009 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8000, 16⟩]
  wr := [⟨0, 0⟩, ⟨0x4000, 624⟩]

/-- The postconditions match on `decrypt`; the result is the low word of `a0`. -/
theorem openTo_verified :
    Verified RISCV64.target Impl.ChaCha20Poly1305.RISCV64.openTo (openToScratchContract RISCV64.abi 78) :=
  Verified.of_correct openTo_ok openTo_ct
    { pre := by
        intro s h
        sig_pre [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | bv_omega_arith
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPost, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg,
          RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToRes] at h
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
          next _ e₂ => exact ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
          [Proof.ChaCha20Poly1305.RISCV64.openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
          using Proof.ChaCha20Poly1305.RISCV64.openToSat }

/-- A state satisfying `open_to`'s precondition, without the working space:
`tag`, its one stack argument. -/
def openToFrameSat : State :=
  { openToSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8000, 8⟩],
                   wr := [⟨0, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract RISCV64.abi 640).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
    RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
    List.range.loop] [openToFrameSat, openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using openToFrameSat

/-- `open_to` with its working space in a frame of 640 bytes on the stack
(after the copy of `tag` and the working space's address), wiped after the
code. -/
theorem openTo_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo)
      (Spec.ChaCha20Poly1305.openToContract RISCV64.abi 640) :=
  RISCV64.Verified.stackScratchArgsWiped (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 78) (pre := Spec.ChaCha20Poly1305.openToPre RISCV64.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 640)
    (m := 1) (words := 78) (leak := some (Spec.ChaCha20Poly1305.openToLeak RISCV64.abi.ptrBits))
    openTo_verified (by decide) (by decide) (by decide) (by decide) (openToPre_local _) (openToPost_local _)
    (openToPost_out _) openToFrameSat_pre (hleak := openToLeak_local _)

end VG.Proof.ChaCha20Poly1305.RISCV64
