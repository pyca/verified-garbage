import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
import VerifiedGarbage.Proof.Modes.Cfb8
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Modes.X86_64.Cfb8

/-!
# CFB8 on x86-64, for any core: the byte and the shift

`cfb8Xor_wp`: the output's first byte XORed into the data's byte, the
ciphertext byte left in `al`. `cfb8Shift_wp`: the input block, at the IV,
shifted left by a byte in place, with `al` shifted in: each byte but the
last is the one after it (`shl1`, one `shiftByte` at a time), and the last
is `al`.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeW8_apply)

variable {c : Core}

/-- `movzx d, byte [r + off]`. -/
theorem ld8_ok (s : State) (d r : Reg) (off : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 off) 1) :
    ∃ s', runBlock isa [.movzx8 d (at_ r off)] s = some s' ∧
      s'.gpr d = (s.mem (s.gpr r + BitVec.ofNat 64 off)).setWidth 64 ∧
      (∀ x, x ≠ d → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d ((s.mem (s.gpr r + BitVec.ofNat 64 off)).setWidth 64), by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, State.load8, State.ea, ofInt_nat, hr,
      ite_true, Option.map_some],
    RegUpd.gpr_setReg_self _ _ _, fun _ hx => RegUpd.gpr_setReg_of_ne _ _ hx, rfl, rfl, rfl⟩

/-- `mov byte [r + off], v`. -/
theorem st8_ok (s : State) (r v : Reg) (off : Nat) (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 off) 1) :
    ∃ s', runBlock isa [.store8 (at_ r off) v] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) ((s.gpr v).setWidth 8) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨{ s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) ((s.gpr v).setWidth 8) }, by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, State.store8, State.ea, ofInt_nat, hw,
      ite_true], rfl, rfl, rfl, rfl⟩

/-- `xor d, r`. -/
theorem xorRR_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [.alu .xor d (.reg r)] s = some s' ∧ s'.gpr d = s.gpr d ^^^ s.gpr r ∧
      (∀ x, x ≠ d → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr d ^^^ s.gpr r) false false).setReg d (s.gpr d ^^^ s.gpr r), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some], ?_,
    fun x h => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags]

theorem setWidth_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem setWidth_xor_byte (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  rw [BitVec.setWidth_xor, setWidth_byte, setWidth_byte]

/-- The output's first byte, at `T` (`sb + 8 buf`), XORed into the data's
byte at `A` (`dataReg`): the data's byte becomes their XOR, and `al` the
ciphertext byte. -/
theorem cfb8Xor_wp (enc : Bool) {s : State} {A T : Addr} (hA : s.gpr c.dataReg = A)
    (hT : s.gpr sb + BitVec.ofNat 64 (8 * c.buf) = T) (da : c.dataReg ≠ .rax) (dbp : c.dataReg ≠ .rbp)
    (wA : InRegions s.wr A 1) (rT : InRegions (s.rd ++ s.wr) T 1) :
    WP isa (.block (c.cfb8Xor enc)) s fun s' => (∀ x, x ≠ .rax → x ≠ .rbp → s'.gpr x = s.gpr x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem.writeW A (s.mem A ^^^ s.mem T) ∧
      (s'.gpr .rax).setWidth 8 = (if enc then s.mem A ^^^ s.mem T else s.mem A) := by
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ld8_ok s .rax c.dataReg 0 (by rw [hA, p0]; exact inRd wA)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ld8_ok s₁ .rbp sb (8 * c.buf)
    (by rw [rd₁, wr₁, o₁ _ (by decide), hT]; exact rT)
  have a₂ : s₂.gpr .rax = (s.mem A).setWidth 64 := by rw [o₂ _ (by decide), v₁, hA, p0]
  have b₂ : s₂.gpr .rbp = (s.mem T).setWidth 64 := by rw [v₂, m₁, o₁ _ (by decide), hT]
  have d₂ : s₂.gpr c.dataReg = A := by rw [o₂ _ dbp, o₁ _ da, hA]
  cases enc
  · obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := xorRR_ok s₂ .rbp .rax
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := st8_ok s₃ c.dataReg .rbp 0
      (by rw [wr₃, wr₂, wr₁, o₃ _ dbp, d₂, p0]; exact wA)
    refine WP.of_runBlock ⟨s₄, ?_, fun x h1 h2 => by rw [g₄, o₃ x h2, o₂ x h2, o₁ x h1], by
      rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
    · simp only [Core.cfb8Xor, Bool.false_eq_true, ite_false]
      rw [show ([.movzx8 .rax (at_ c.dataReg 0), .movzx8 .rbp (at_ sb (8 * c.buf)), .alu .xor .rbp (.reg .rax),
        .store8 (at_ c.dataReg 0) .rbp] : List Instr) = [.movzx8 .rax (at_ c.dataReg 0)] ++
        ([.movzx8 .rbp (at_ sb (8 * c.buf))] ++ ([.alu .xor .rbp (.reg .rax)] ++
        [.store8 (at_ c.dataReg 0) .rbp])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
        Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
    · rw [m₄, m₃, m₂, m₁, o₃ _ dbp, d₂, p0, v₃, a₂, b₂, setWidth_xor_byte, BitVec.xor_comm]
    · rw [g₄, o₃ _ (by decide), a₂, setWidth_byte]; rfl
  · obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := xorRR_ok s₂ .rax .rbp
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := st8_ok s₃ c.dataReg .rax 0
      (by rw [wr₃, wr₂, wr₁, o₃ _ da, d₂, p0]; exact wA)
    refine WP.of_runBlock ⟨s₄, ?_, fun x h1 h2 => by rw [g₄, o₃ x h1, o₂ x h2, o₁ x h1], by
      rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], ?_, ?_⟩
    · simp only [Core.cfb8Xor, ite_true]
      rw [show ([.movzx8 .rax (at_ c.dataReg 0), .movzx8 .rbp (at_ sb (8 * c.buf)), .alu .xor .rax (.reg .rbp),
        .store8 (at_ c.dataReg 0) .rax] : List Instr) = [.movzx8 .rax (at_ c.dataReg 0)] ++
        ([.movzx8 .rbp (at_ sb (8 * c.buf))] ++ ([.alu .xor .rax (.reg .rbp)] ++
        [.store8 (at_ c.dataReg 0) .rax])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂,
        Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
    · rw [m₄, m₃, m₂, m₁, o₃ _ da, d₂, p0, v₃, a₂, b₂, setWidth_xor_byte]
    · rw [g₄, v₃, a₂, b₂, setWidth_xor_byte]; rfl

/-- `m` with each of the first `i` bytes at `P` replaced by the byte after
it. -/
def shl1 (m : Mem) (P : Addr) (i : Nat) : Mem := fun x => if (x - P).toNat < i then m (x + 1) else m x

theorem shl1_zero (m : Mem) (P : Addr) : shl1 m P 0 = m := by funext x; simp [shl1]

theorem sub_eq_iff {x P : Addr} {i : Nat} (hi : i < 2 ^ 64) : x = P + BitVec.ofNat 64 i ↔ (x - P).toNat = i := by
  constructor
  · rintro rfl; rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  · intro h
    have : x - P = BitVec.ofNat 64 i := BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi])
    rw [← this, BitVec.add_comm, BitVec.sub_add_cancel]

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 i + 1 := by
  rw [← BitVec.ofNat_add_ofNat]; rfl

/-- The shift's byte moves, then the last byte. -/
theorem cfb8Shift_wp {s : State} {P : Addr} (hc : s.gpr .rcx = P) (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr)
    (hbw : 0 < c.bw) (hbw2 : c.bw ≤ 2) :
    WP isa (.block c.cfb8Shift) s fun s' => (∀ x, x ≠ .rbp → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ u < 8 * c.bw, s'.mem (P + BitVec.ofNat 64 u) =
        if u + 1 < 8 * c.bw then s.mem (P + BitVec.ofNat 64 (u + 1)) else (s.gpr .rax).setWidth 8) ∧
      Frame [⟨P, 8 * c.bw⟩] s.mem s'.mem := by
  have c₁ := hc
  have rd₁ : s.rd = s.rd := rfl
  have wr₁ : s.wr = s.wr := rfl
  have m₁ : s.mem = s.mem := rfl
  have inP : ∀ {u}, u < 8 * c.bw → InRegions s.wr (P + BitVec.ofNat 64 u) 1 := fun hu =>
    ⟨_, hwP, VG.Offset.contains_base P (by omega) (by omega)⟩
  -- The byte moves.
  have hmv : WP isa (.block ((List.range (8 * c.bw - 1)).flatMap Core.shiftByte)) s fun s₂ =>
      (∀ x, x ≠ .rbp → s₂.gpr x = s.gpr x) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
        s₂.mem = shl1 s.mem P (8 * c.bw - 1) := by
    refine wp_range_flatMap (M := isa) (N := 8 * c.bw - 1) (fun i s₂ => (∀ x, x ≠ .rbp → s₂.gpr x = s.gpr x) ∧
        s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = shl1 s.mem P i)
      (fun i s₂ hi ⟨g₂, rd₂, wr₂, m₂⟩ => ?_) _ (Nat.le_refl _) s ⟨fun _ _ => rfl, rfl, rfl, by rw [shl1_zero]⟩
    have hc : s₂.gpr .rcx = P := by rw [g₂ _ (by decide), c₁]
    obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := ld8_ok s₂ .rbp .rcx (i + 1)
      (by rw [rd₂, wr₂, rd₁, wr₁, hc]; exact inRd (inP (by omega)))
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := st8_ok s₃ .rcx .rbp i
      (by rw [wr₃, wr₂, wr₁, o₃ _ (by decide), hc]; exact inP (by omega))
    refine WP.of_runBlock ⟨s₄, by
      rw [Core.shiftByte, show ([.movzx8 .rbp (at_ .rcx (i + 1)), .store8 (at_ .rcx i) .rbp] : List Instr) =
        [.movzx8 .rbp (at_ .rcx (i + 1))] ++ [.store8 (at_ .rcx i) .rbp] from rfl, runBlock_app, e₃,
        Option.bind_some, e₄],
      fun x hx => by rw [g₄, o₃ x hx, g₂ x hx], by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂], ?_⟩
    rw [m₄, m₃, o₃ _ (by decide), v₃, hc, setWidth_byte, m₂]
    funext x
    rw [writeW8_apply]
    have h64 : 8 * c.bw < 2 ^ 64 := by omega
    have hP1 : shl1 s.mem P i (P + BitVec.ofNat 64 (i + 1)) = s.mem (P + BitVec.ofNat 64 (i + 1)) := by
      simp only [shl1]; rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        ite_eq_right (by omega)]
    rw [hP1]
    by_cases hx : x = P + BitVec.ofNat 64 i
    · rw [ite_eq_left hx]
      simp only [shl1]
      rw [ite_eq_left (by rw [(sub_eq_iff (by omega)).mp hx]; omega), hx, BitVec.add_assoc, ofNat_succ]
    · rw [ite_eq_right hx]
      have hne : (x - P).toNat ≠ i := fun h => hx ((sub_eq_iff (by omega)).mpr h)
      simp only [shl1]
      by_cases h1 : (x - P).toNat < i
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  refine WP.block_append (WP.mono hmv fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_)
  have hc : s₂.gpr .rcx = P := by rw [g₂ _ (by decide), c₁]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := st8_ok s₂ .rcx .rax (8 * c.bw - 1)
    (by rw [wr₂, wr₁, hc]; exact inP (by omega))
  refine WP.of_runBlock ⟨s₃, e₃, fun x h2 => by rw [g₃, g₂ x h2], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], fun u hu => ?_, ?_⟩
  · rw [m₃, hc, writeW8_apply, g₂ _ (by decide), m₂, m₁]
    by_cases hl : u + 1 < 8 * c.bw
    · rw [ite_eq_right (fun h => by
        have := (sub_eq_iff (x := P + BitVec.ofNat 64 u) (P := P) (by omega)).mp h
        rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        omega), ite_eq_left hl]
      simp only [shl1]
      rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega),
        BitVec.add_assoc, ofNat_succ]
    · rw [ite_eq_left (by congr 2; omega), ite_eq_right hl]
  · rw [m₃, hc, m₂, m₁]
    intro x hx
    have hx' : ¬ (x - P).toNat < 8 * c.bw := fun h => hx _ List.mem_cons_self (by
      simp only [Region.Contains]; omega)
    rw [writeW8_apply, ite_eq_right (fun h => hx' (by rw [(sub_eq_iff (by omega)).mp h]; omega))]
    simp only [shl1]
    rw [ite_eq_right (by omega)]

end VG.Proof.Modes.X86_64
