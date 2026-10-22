module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Frame
public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Scanning the public q for its significant bytes (32-bit ARM)

`significant` reads the `q_len` bytes of q from its first, keeping the
count of bytes from the first nonzero one (`r3`) and that byte (`r4`):
`VG.Proof.Dsa.significant`. Its branches are on q's bytes, which are public.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_subs wp_ldrb op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Dsa (scanNext scanFinish scanFinish_step scanFinish_nil)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `cmp n, #0`. -/
theorem wp_cmp0 {n : Reg} (k : ∀ s', Fupd s s' → s'.z = (s.gpr n == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n (.imm 0) :: is)) s Q :=
  wp_cmp (op2_imm (by decide)) fun s' f z => k s' f (by rw [z]; exact congrArg (· == 0) (BitVec.sub_zero _))

/-- `subs d, d, #1`. -/
theorem wp_dec {d : Reg} (k : ∀ s', Upd s s' d (s.gpr d - 1) → s'.z = (s.gpr d - 1 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d d (.imm 1) :: is)) s Q :=
  wp_subs (op2_imm (by decide)) k

/-- `add d, d, #1`. -/
theorem wp_inc {d : Reg} (k : ∀ s', Upd s s' d (s.gpr d + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d d (.imm 1) :: is)) s Q :=
  wp_dp (op2_imm (by decide)) k

end

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 32).toNat = 1 from rfl]
  omega

theorem byte_beq_zero (b : Byte) : (b.setWidth 32 == 0) = decide (b = 0) := by
  by_cases hb0 : b = 0
  · subst hb0; rfl
  · simp only [hb0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply hb0; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    rw [VG.Proof.Dsa.toNat_setWidth8] at this
    rw [this]; rfl

/-- The scan's state, with `rest` to read. -/
structure ScanState (s : State) (p : BitVec 32) (rest : List Byte) (found : Nat × Byte) : Prop where
  r1 : s.gpr .r1 = p
  r2 : s.gpr .r2 = BitVec.ofNat 32 rest.length
  r3 : s.gpr .r3 = BitVec.ofNat 32 found.1
  r4 : s.gpr .r4 = found.2.setWidth 32
  bytes : BytesIn s p rest
  bound : found.1 < 2 ^ 32
  zero : found.1 = 0 → found.2 = 0

abbrev scanRegs : List Reg := [.r0, .r1, .r2, .r3, .r4]

theorem significantByte_ok {s : State} {p : BitVec 32} {b : Byte} {rest : List Byte} {found : Nat × Byte}
    (h : ScanState s p (b :: rest) found) (hl : rest.length + 1 < 2 ^ 32) :
    WP isa significantByte s fun t =>
      ScanState t (p + 1) rest (scanNext found (rest.length + 1) b) ∧
      t.z = decide (rest.length = 0) ∧ t.mem = s.mem ∧ Rest scanRegs s t := by
  have hb : s.mem (State.addr p) = b := by
    have := h.bytes.val 0 (by simp)
    simpa only [BitVec.add_zero, List.getElem_cons_zero] using this
  have hr : InRegions (s.rd ++ s.wr) (State.addr p) 1 := by
    simpa only [BitVec.add_zero] using h.bytes.rd 0 (by simp)
  unfold significantByte significantChoose
  refine WP.seq (wp_ldrb (by decide) (by rw [BitVec.add_zero, h.r1]) hr fun s₁ u₁ => WP.block_nil ?_)
  rw [hb] at u₁
  -- The choice, then the step.
  have after : ∀ (u : State), u.gpr .r3 = BitVec.ofNat 32 (scanNext found (rest.length + 1) b).1 →
      u.gpr .r4 = (scanNext found (rest.length + 1) b).2.setWidth 32 → u.mem = s.mem →
      Rest scanRegs s u → u.gpr .r1 = p → u.gpr .r2 = BitVec.ofNat 32 (rest.length + 1) →
      WP isa (.block [.dp .add .r1 .r1 (.imm 1), .subs .r2 .r2 (.imm 1)]) u fun t =>
        ScanState t (p + 1) rest (scanNext found (rest.length + 1) b) ∧
        t.z = decide (rest.length = 0) ∧ t.mem = s.mem ∧ Rest scanRegs s t := by
    intro u h3 h4 hm R e1 e2
    refine wp_inc fun s₂ u₂ => wp_dec fun s₃ u₃ z₃ => WP.block_nil ?_
    have R₃ : Rest scanRegs s s₃ := R.trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
    have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, hm]
    have hcx : s₃.gpr .r2 = BitVec.ofNat 32 rest.length := by
      rw [u₃.gpr, u₂.other _ (by decide), e2, ofNat_sub_one (by omega), Nat.add_sub_cancel]
    have hbnd : (scanNext found (rest.length + 1) b).1 < 2 ^ 32 ∧
        ((scanNext found (rest.length + 1) b).1 = 0 → (scanNext found (rest.length + 1) b).2 = 0) := by
      unfold scanNext
      split
      · exact ⟨hl, fun e => by simp only at e; omega⟩
      · exact ⟨h.bound, h.zero⟩
    refine ⟨⟨?_, hcx, by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact h3,
      by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact h4, ?_, hbnd.1, hbnd.2⟩, ?_, hm₃, R₃⟩
    · rw [u₃.other _ (by decide), u₂.gpr, e1]
    · have := (h.bytes.drop 1 (by simp)).congr hm₃ (by rw [R₃.rd]) (by rw [R₃.wr])
      rw [List.drop_one, List.tail_cons] at this
      exact this
    · rw [z₃, u₂.other _ (by decide), e2, ofNat_sub_one (by omega), Nat.add_sub_cancel, ofNat_beq_zero (by omega)]
  have R₁ : Rest scanRegs s s₁ := u₁.rest (by decide)
  have e1 : s₁.gpr .r1 = p := by rw [u₁.other _ (by decide), h.r1]
  have e2 : s₁.gpr .r2 = BitVec.ofNat 32 (rest.length + 1) := by rw [u₁.other _ (by decide), h.r2]; rfl
  refine WP.seq (WP.seq (wp_cmp0 fun s₂ f₂ z₂ => WP.block_nil ?_))
  rw [u₁.other _ (by decide), h.r3, ofNat_beq_zero h.bound] at z₂
  by_cases hf0 : found.1 = 0
  · refine WP.ite true (by rw [eval_eq, z₂]; simp [hf0]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.seq (wp_cmp0 fun s₃ f₃ z₃ => WP.block_nil ?_)
    rw [f₂.gpr, u₁.gpr, byte_beq_zero] at z₃
    by_cases hb0 : b = 0
    · refine WP.ite false (by rw [eval_ne, z₃]; simp [hb0]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      have hs : scanNext found (rest.length + 1) b = found := by simp [scanNext, hb0]
      refine after s₃ (by rw [hs, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.r3])
        (by rw [hs, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.r4]) (by rw [f₃.mem, f₂.mem, u₁.mem])
        (R₁.trans ((f₂.rest _).trans (f₃.rest _))) (by rw [f₃.gpr, f₂.gpr, e1]) (by rw [f₃.gpr, f₂.gpr, e2])
    · refine WP.ite true (by rw [eval_ne, z₃, decide_eq_false hb0]; rfl)
        (fun _ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_)
        (fun e => Bool.noConfusion e)
      have hs : scanNext found (rest.length + 1) b = (rest.length + 1, b) := by
        simp only [scanNext, hf0, ne_eq, hb0, not_false_eq_true, and_self, ite_true]
      refine after s₅ ?_ ?_ (by rw [u₅.mem, u₄.mem, f₃.mem, f₂.mem, u₁.mem]) ?_ ?_ ?_
      · rw [hs, u₅.other _ (by decide), u₄.gpr, f₃.gpr, f₂.gpr, e2]
      · rw [hs, u₅.gpr, u₄.other _ (by decide), f₃.gpr, f₂.gpr, u₁.gpr]
      · exact R₁.trans ((f₂.rest _).trans ((f₃.rest _).trans ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
      · rw [u₅.other _ (by decide), u₄.other _ (by decide), f₃.gpr, f₂.gpr, e1]
      · rw [u₅.other _ (by decide), u₄.other _ (by decide), f₃.gpr, f₂.gpr, e2]
  · refine WP.ite false (by rw [eval_eq, z₂]; simp [hf0]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    have hs : scanNext found (rest.length + 1) b = found := by simp [scanNext, hf0]
    exact after s₂ (by rw [hs, f₂.gpr, u₁.other _ (by decide), h.r3])
      (by rw [hs, f₂.gpr, u₁.other _ (by decide), h.r4]) (by rw [f₂.mem, u₁.mem])
      (R₁.trans (f₂.rest _)) (by rw [f₂.gpr, e1]) (by rw [f₂.gpr, e2])

/-- Scan a nonempty q, leading zero padding included. -/
theorem significant_ok {s : State} {p : BitVec 32} {bs : List Byte}
    (h1 : s.gpr .r1 = p) (h2 : s.gpr .r2 = BitVec.ofNat 32 bs.length)
    (hb : BytesIn s p bs) (hn : 0 < bs.length) (h32 : bs.length < 2 ^ 32) :
    WP isa Random.significant s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .r4 = (VG.Proof.Dsa.significant bs).2.setWidth 32 ∧ t.mem = s.mem ∧ Rest scanRegs s t := by
  unfold Random.significant
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have R₂ : Rest scanRegs s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have h₀ : ScanState s₂ p bs (0, 0) :=
    ⟨by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h1,
      by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h2,
      by rw [u₂.other _ (by decide), u₁.gpr]; rfl, by rw [u₂.gpr]; rfl,
      hb.congr m₂ R₂.rd R₂.wr, by decide, fun _ => rfl⟩
  refine WP.loop (M := isa) (fun n t => ∃ (j : Nat) (found : Nat × Byte), (bs.drop j).length = n ∧ 0 < n ∧
      ScanState t (p + BitVec.ofNat 32 j) (bs.drop j) found ∧
      scanFinish found (bs.drop j) = VG.Proof.Dsa.significant bs ∧
      t.mem = s.mem ∧ Rest scanRegs s t) ?_ bs.length s₂
    ⟨0, (0, 0), by simp, hn, by simpa only [BitVec.add_zero, List.drop_zero] using h₀, by simp [scanFinish],
      m₂, R₂⟩
  rintro n t ⟨j, found, hlen, hpos, ht, htarget, htm, hkt⟩
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, bs.drop j = b :: rest := by
    cases e : bs.drop j with
    | nil => rw [e] at hlen; simp at hlen; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  rw [hbr] at ht htarget hlen
  have hrl : rest.length + 1 = bs.length - j := by
    have := congrArg List.length hbr; simp only [List.length_drop, List.length_cons] at this; omega
  refine WP.mono (significantByte_ok ht (by omega)) fun u ⟨hu, hz, hum, hku⟩ => ?_
  have hrest : bs.drop (j + 1) = rest := by
    rw [← List.drop_drop, hbr, List.drop_one, List.tail_cons]
  have hu' : ScanState u (p + BitVec.ofNat 32 (j + 1)) (bs.drop (j + 1))
      (scanNext found (rest.length + 1) b) := by
    rw [hrest, BitVec.ofNat_add, ← BitVec.add_assoc]; exact hu
  have htarget' := (scanFinish_step found b rest).trans htarget
  have hk := hkt.trans hku
  by_cases he : rest.length = 0
  · left
    have hnil := (congrArg (scanFinish _) (List.length_eq_zero_iff.mp he)).trans (scanFinish_nil hu.zero)
    refine ⟨by rw [eval_ne, hz, he]; rfl, ?_, ?_, hum.trans htm, hk⟩
    · rw [hu.r3, ← hnil.symm.trans htarget']
    · rw [hu.r4, ← hnil.symm.trans htarget']
  · right
    refine ⟨by rw [eval_ne, hz]; simp [he], rest.length, by simp only [List.length_cons] at hlen; omega,
      j + 1, _, by rw [hrest], by omega, hu', by rw [hrest]; exact htarget', hum.trans htm, hk⟩

end VG.Proof.Dsa.Arm.Key
