module

-- separate module: the digits block, a stage of `xmssPk`'s proof rebuilt only when it changes

public import VerifiedGarbage.Proof.Framework.X86_64.Steps
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Xmss
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# SLH-DSA on x86-64: the digits of a message

`Xmss.digits` (`Impl/SlhDsa/X86_64/Xmss.lean`) stores, from the `n` bytes
at `r15`, the two halves of each, high first, to the bytes from
`rbx + oDigits` (`digitByte_ok`, one byte at a time), summing them in
`r10`. This file runs the code of one byte: the rules for `shr` and `and`
by an immediate in the style of `Proof/Framework/X86_64/Steps.lean`, and
the step of the stores of one byte of the message.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64 VG.X86_64.Steps
open VG.Impl.Sha3.X86_64 (at_)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `shr d, n`, `1 ≤ n ≤ 63`. -/
theorem wp_shri {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  have e : exec (.shift .shr d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
      (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
      (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  refine WP.cons e (k _ ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h],
    rfl, rfl, rfl, rfl⟩)

/-- `and d, imm32` (sign-extended). -/
theorem wp_andi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]; congr 1

theorem sx15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide

theorem hi_nat (x : Byte) : ((x.setWidth 64 >>> 4).setWidth 8 : Byte) = BitVec.ofNat 8 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt; omega

theorem lo_nat (x : Byte) : ((x.setWidth 64 &&& 15).setWidth 8 : Byte) = BitVec.ofNat 8 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt; omega

theorem hi64 (x : Byte) : (x.setWidth 64 >>> 4 : BitVec 64) = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt; omega

theorem lo64 (x : Byte) : (x.setWidth 64 &&& 15 : BitVec 64) = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt; omega

/-- The stores of byte `b` of the message: its two halves to digits `2b` and
`2b + 1`, their sum added to `r10`; only `rax`, `rcx` and `r10` change. -/
theorem digitByte_ok (b : Nat) {is : List Instr} {s : State} {Q : State → Prop} {S Mp : Addr}
    (hbx : s.gpr .rbx = S) (h15 : s.gpr .r15 = Mp)
    (hin : InRegions (s.rd ++ s.wr) (Mp + BitVec.ofNat 64 b) 1)
    (hw₁ : InRegions s.wr (S + BitVec.ofNat 64 (Impl.SlhDsa.X86_64.Layout.oDigits + 2 * b)) 1)
    (hw₂ : InRegions s.wr (S + BitVec.ofNat 64 (Impl.SlhDsa.X86_64.Layout.oDigits + 2 * b + 1)) 1)
    (k : ∀ s', s'.mem = (s.mem.writeW (S + BitVec.ofNat 64 (Impl.SlhDsa.X86_64.Layout.oDigits + 2 * b))
          (BitVec.ofNat 8 ((s.mem (Mp + BitVec.ofNat 64 b)).toNat / 16))).writeW
          (S + BitVec.ofNat 64 (Impl.SlhDsa.X86_64.Layout.oDigits + 2 * b + 1))
          (BitVec.ofNat 8 ((s.mem (Mp + BitVec.ofNat 64 b)).toNat % 16)) →
      s'.gpr .r10 = s.gpr .r10 + BitVec.ofNat 64 ((s.mem (Mp + BitVec.ofNat 64 b)).toNat / 16 +
        (s.mem (Mp + BitVec.ofNat 64 b)).toNat % 16) →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Xmss.digitByte b ++ is)) s Q := by
  simp only [Impl.SlhDsa.X86_64.Xmss.digitByte, List.cons_append, List.nil_append]
  refine wp_movzx8 (by rw [ea_at', h15]) hin fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => ?_
  refine wp_shri (by decide) (by decide) fun s₃ u₃ => ?_
  have r3 : s₃.gpr .rax = BitVec.ofNat 64 ((s.mem (Mp + BitVec.ofNat 64 b)).toNat / 16) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hi64]
  have b3 : s₃.gpr .rbx = S := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx]
  refine wp_store8 (by rw [ea_at', b3]) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw₁) fun s₄ u₄ => ?_
  refine wp_andi fun s₅ u₅ => ?_
  have r5 : s₅.gpr .rcx = BitVec.ofNat 64 ((s.mem (Mp + BitVec.ofNat 64 b)).toNat % 16) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, sx15, lo64]
  have a5 : s₅.gpr .rax = BitVec.ofNat 64 ((s.mem (Mp + BitVec.ofNat 64 b)).toNat / 16) := by
    rw [u₅.other _ (by decide), u₄.gpr, r3]
  have b5 : s₅.gpr .rbx = S := by rw [u₅.other _ (by decide), u₄.gpr, b3]
  refine wp_store8 (by rw [ea_at', b5]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw₂) fun s₆ u₆ => ?_
  refine wp_add fun s₇ u₇ => ?_
  refine wp_add fun s₈ u₈ => ?_
  have setw8 : ∀ v : Nat, (BitVec.ofNat 64 v).setWidth 8 = BitVec.ofNat 8 v := fun v => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd v (by decide)
  refine k s₈ ?_ ?_ ?_ ?_ ?_
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, r5, r3, setw8, setw8]
  · rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, r5, a5, u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add]
  · intro r h₁ h₂ h₃
    rw [u₈.other _ h₃, u₇.other _ h₃, u₆.gpr, u₅.other _ h₂, u₄.gpr, u₃.other _ h₁, u₂.other _ h₂,
      u₁.other _ h₁]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## All the bytes -/

open VG.Impl.SlhDsa.X86_64 (Layout)

/-- Byte `b` of the message at `S + oMsg`. -/
def msgByte (m : Mem) (S : Addr) (b : Nat) : Nat := (m (S + BitVec.ofNat 64 (Layout.oMsg + b))).toNat

/-- The memory after the stores of the first `b` bytes of the message. -/
def dmem (m : Mem) (S : Addr) : Nat → Mem
  | 0 => m
  | b + 1 => ((dmem m S b).writeW (S + BitVec.ofNat 64 (Layout.oDigits + 2 * b))
      (BitVec.ofNat 8 (msgByte m S b / 16))).writeW (S + BitVec.ofNat 64 (Layout.oDigits + 2 * b + 1))
      (BitVec.ofNat 8 (msgByte m S b % 16))

/-- The sum of the digits of the first `b` bytes. -/
def dsum (m : Mem) (S : Addr) : Nat → Nat
  | 0 => 0
  | b + 1 => dsum m S b + (msgByte m S b / 16 + msgByte m S b % 16)

theorem writeB_other (m : Mem) {a x : Addr} (v : Byte) (h : x ≠ a) : (m.writeW a v) x = m x :=
  Mem.write_apply (by intro h'; apply h; bv_omega)

theorem writeB_self (m : Mem) (a : Addr) (v : Byte) : (m.writeW a v) a = v := by
  simp [Mem.writeW, Mem.write]

theorem ne_off (S : Addr) {a c : Nat} (ha : a < 65536) (hc : c < 65536) (h : a ≠ c) :
    S + BitVec.ofNat 64 a ≠ S + BitVec.ofNat 64 c := Offset.add_ofNat_ne S (by omega) (by omega) h

/-- `dmem` keeps every byte but the digits'. -/
theorem dmem_other (m : Mem) (S : Addr) {o : Nat} (ho : o < 65536) :
    ∀ b, b ≤ 64 → (o < Layout.oDigits ∨ Layout.oDigits + 2 * b ≤ o) →
      dmem m S b (S + BitVec.ofNat 64 o) = m (S + BitVec.ofNat 64 o)
  | 0, _, _ => rfl
  | b + 1, hb, h => by
    have : Layout.oDigits = 30368 := rfl
    simp only [dmem]
    rw [writeB_other _ _ (ne_off S ho (by omega) (by omega)), writeB_other _ _ (ne_off S ho (by omega) (by omega)),
      dmem_other m S ho b (by omega) (by omega)]

theorem msgByte_dmem (m : Mem) (S : Addr) {b q : Nat} (hb : b ≤ 64) (hq : q < 64) :
    (dmem m S b (S + BitVec.ofNat 64 (Layout.oMsg + q))).toNat = msgByte m S q := by
  have : Layout.oDigits = 30368 := rfl
  have : Layout.oMsg = 30496 := rfl
  rw [dmem_other m S (by omega) b hb (by omega)]
  rfl

/-- Digit `j` of the first bytes: the high half of byte `j / 2` for an even
`j`, the low half for an odd one. -/
def nibD (m : Mem) (S : Addr) (j : Nat) : Nat :=
  if j % 2 = 0 then msgByte m S (j / 2) / 16 else msgByte m S (j / 2) % 16

theorem dmem_digit (m : Mem) (S : Addr) : ∀ b, b ≤ 64 → ∀ j < 2 * b,
    dmem m S b (S + BitVec.ofNat 64 (Layout.oDigits + j)) = BitVec.ofNat 8 (nibD m S j)
  | 0, _, j, hj => absurd hj (by omega)
  | b + 1, hb, j, hj => by
    have : Layout.oDigits = 30368 := rfl
    simp only [dmem]
    by_cases h1 : j = 2 * b + 1
    · subst h1; rw [← Nat.add_assoc, writeB_self]; simp only [nibD]; rw [ite_eq_right (by omega)]; congr 3; omega
    · rw [writeB_other _ _ (ne_off S (by omega) (by omega) (by omega))]
      by_cases h0 : j = 2 * b
      · subst h0; rw [writeB_self]; simp only [nibD]; rw [ite_eq_left (by omega)]; congr 3; omega
      · rw [writeB_other _ _ (ne_off S (by omega) (by omega) (by omega)), dmem_digit m S b (by omega) j (by omega)]

theorem addr_add (S : Addr) (a b : Nat) : S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The stores of bytes `b` to `b + c - 1` of the message, from the memory
after those before them. -/
theorem bytes_ok (n : Nat) (hn : n ≤ 64) (m : Mem) (S : Addr) :
    ∀ c b, b + c = n → ∀ {s : State} {is : List Instr} {Q : State → Prop},
      s.mem = dmem m S b → s.gpr .rbx = S → s.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg →
      s.gpr .r10 = BitVec.ofNat 64 (dsum m S b) →
      (∀ o, o + 1 ≤ 65536 → InRegions s.wr (S + BitVec.ofNat 64 o) 1) →
      (∀ o, o + 1 ≤ 65536 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 o) 1) →
      (∀ s', s'.mem = dmem m S n → s'.gpr .r10 = BitVec.ofNat 64 (dsum m S n) →
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
        WP isa (.block is) s' Q) →
      WP isa (.block ((List.range' b c).flatMap Impl.SlhDsa.X86_64.Xmss.digitByte ++ is)) s Q
  | 0, b, hbc, s, is, Q, hm, _, _, h10, _, _, k => by
    have : b = n := by omega
    subst this
    exact k s hm h10 (fun _ _ _ _ => rfl) rfl rfl
  | c + 1, b, hbc, s, is, Q, hm, hbx, h15, h10, hW, hR, k => by
    have : Layout.oDigits = 30368 := rfl
    have : Layout.oMsg = 30496 := rfl
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine digitByte_ok b hbx h15 (by rw [addr_add]; exact hR _ (by omega)) (hW _ (by omega)) (hW _ (by omega))
      fun s' hm' h10' hk hrd hwr => ?_
    rw [addr_add, hm, msgByte_dmem m S (by omega) (by omega)] at hm' h10'
    refine bytes_ok n hn m S c (b + 1) (by omega) (s := s') (by rw [hm']; rfl) (by rw [hk _ (by decide) (by decide) (by decide), hbx])
      (by rw [hk _ (by decide) (by decide) (by decide), h15])
      (by rw [h10', h10, ← BitVec.ofNat_add]; rfl) (fun o ho => by rw [hwr]; exact hW o ho)
      (fun o ho => by rw [hrd, hwr]; exact hR o ho) fun s'' a b' c' d e => k s'' a b'
        (fun r h₁ h₂ h₃ => by rw [c' r h₁ h₂ h₃, hk r h₁ h₂ h₃]) (by rw [d, hrd]) (by rw [e, hwr])

/-! ## The checksum -/

theorem setw8 (v : Nat) : (BitVec.ofNat 64 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem and15 (v : Nat) (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v &&& BitVec.signExtend 64 (15 : BitVec 32)) =
    BitVec.ofNat 64 (v % 16) := by
  rw [sx15]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr_ofNat (v k : Nat) (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> k : BitVec 64) = BitVec.ofNat 64 (v / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv)]

theorem sub_ofNat' {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The three checksum digits stored by the tail of `Xmss.digits`, from
`cs` (below `2⁶⁴`, in `r11`). -/
def csumMem (m : Mem) (S : Addr) (n cs : Nat) : Mem :=
  (((((m.writeW (S + BitVec.ofNat 64 (Layout.oDigits + 2 * n)) (BitVec.ofNat 8 (cs / 2 ^ 8 % 16))).writeW
    (S + BitVec.ofNat 64 (Layout.oDigits + 2 * n + 1)) (BitVec.ofNat 8 (cs / 2 ^ 4 % 16))).writeW
    (S + BitVec.ofNat 64 (Layout.oDigits + 2 * n + 2)) (BitVec.ofNat 8 (cs % 16))).writeW
    (S + BitVec.ofNat 64 (Layout.oVar 1 0)) (0 : BitVec 64)).writeW (S + BitVec.ofNat 64 (Layout.oVar 1 1)) (0 : BitVec 64))

theorem mov32_zero : ((0 : BitVec 32).setWidth 64 : BitVec 64) = 0 := by decide

/-- The tail of `Xmss.digits`: from `r10` holding the sum of the digits,
the checksum's three digits, and the frame's variables 0 and 1 zeroed. -/
theorem tail_ok (L : Layout) {s : State} {S : Addr} {is : List Instr} {Q : State → Prop} {σ : Nat}
    (hn : L.n ≤ 64) (hσ : σ ≤ 15 * 2 * L.n) (hbx : s.gpr .rbx = S) (h10 : s.gpr .r10 = BitVec.ofNat 64 σ)
    (hW : ∀ o, o + 8 ≤ 65536 → InRegions s.wr (S + BitVec.ofNat 64 o) 8)
    (hW1 : ∀ o, o + 1 ≤ 65536 → InRegions s.wr (S + BitVec.ofNat 64 o) 1)
    (k : ∀ s', s'.mem = csumMem s.mem S L.n (15 * 2 * L.n - σ) →
      (∀ r, r ≠ .rax → r ≠ .r11 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (([.mov32 .r11 (.imm (BitVec.ofNat 32 (15 * 2 * L.n))), .alu .sub .r11 (.reg .r10),
      .mov .rax (.reg .r11), .shift .shr .rax 8, .alu .and .rax (.imm 15),
        .store8 (at_ .rbx (Layout.oDigits + 2 * L.n)) .rax,
      .mov .rax (.reg .r11), .shift .shr .rax 4, .alu .and .rax (.imm 15),
        .store8 (at_ .rbx (Layout.oDigits + 2 * L.n + 1)) .rax,
      .mov .rax (.reg .r11), .alu .and .rax (.imm 15), .store8 (at_ .rbx (Layout.oDigits + 2 * L.n + 2)) .rax,
      .mov32 .rax (.imm 0), .store (at_ .rbx (Layout.oVar 1 0)) .rax, .store (at_ .rbx (Layout.oVar 1 1)) .rax] : List Instr) ++ is))
      s Q := by
  have : Layout.oDigits = 30368 := rfl
  have : Layout.oVar 1 0 = 2576 := rfl
  have : Layout.oVar 1 1 = 2584 := rfl
  have h30 : 15 * 2 * L.n < 2 ^ 31 := by omega
  obtain ⟨cs, hcs⟩ : ∃ cs, cs = 15 * 2 * L.n - σ := ⟨_, rfl⟩
  have hcs64 : cs < 2 ^ 64 := by omega
  simp only [List.cons_append, List.nil_append]
  refine wp_mov32i fun s₁ u₁ => wp_sub fun s₂ u₂ => ?_
  have r2 : s₂.gpr .r11 = BitVec.ofNat 64 cs := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h10, hcs, ← sub_ofNat' hσ (by omega)]
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have h1 : 15 * 2 * L.n < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]
  have b2 : s₂.gpr .rbx = S := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hbx]
  refine wp_mov fun s₃ u₃ => wp_shri (by decide) (by decide) fun s₄ u₄ => wp_andi fun s₅ u₅ => ?_
  have a5 : s₅.gpr .rax = BitVec.ofNat 64 (cs / 2 ^ 8 % 16) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, r2, shr_ofNat _ _ hcs64, and15 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hcs64)]
  have b5 : s₅.gpr .rbx = S := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), b2]
  have w5 : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_store8 (by rw [ea_at', b5]) (by rw [w5]; exact hW1 _ (by omega)) fun s₆ u₆ => ?_
  refine wp_mov fun s₇ u₇ => wp_shri (by decide) (by decide) fun s₈ u₈ => wp_andi fun s₉ u₉ => ?_
  have r6 : s₆.gpr .r11 = BitVec.ofNat 64 cs := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r2]
  have a9 : s₉.gpr .rax = BitVec.ofNat 64 (cs / 2 ^ 4 % 16) := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, r6, shr_ofNat _ _ hcs64, and15 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hcs64)]
  have b9 : s₉.gpr .rbx = S := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, b5]
  have w9 : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w5]
  refine wp_store8 (by rw [ea_at', b9]) (by rw [w9]; exact hW1 _ (by omega)) fun s₁₀ u₁₀ => ?_
  refine wp_mov fun s₁₁ u₁₁ => wp_andi fun s₁₂ u₁₂ => ?_
  have r10' : s₁₀.gpr .r11 = BitVec.ofNat 64 cs := by
    rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r6]
  have a12 : s₁₂.gpr .rax = BitVec.ofNat 64 (cs % 16) := by rw [u₁₂.gpr, u₁₁.gpr, r10', and15 _ hcs64]
  have b12 : s₁₂.gpr .rbx = S := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, b9]
  have w12 : s₁₂.wr = s.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, w9]
  refine wp_store8 (by rw [ea_at', b12]) (by rw [w12]; exact hW1 _ (by omega)) fun s₁₃ u₁₃ => ?_
  refine wp_mov32i fun s₁₄ u₁₄ => ?_
  have b14 : s₁₄.gpr .rbx = S := by rw [u₁₄.other _ (by decide), u₁₃.gpr, b12]
  have w14 : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, w12]
  refine wp_store (by rw [ea_at', b14]) (by rw [w14]; exact hW _ (by omega)) fun s₁₅ u₁₅ => ?_
  refine wp_store (by rw [ea_at', u₁₅.gpr, b14]) (by rw [u₁₅.wr, w14]; exact hW _ (by omega)) fun s₁₆ u₁₆ => ?_
  refine k s₁₆ ?_ ?_ ?_ ?_
  · rw [u₁₆.mem, u₁₅.gpr, u₁₅.mem, u₁₄.gpr, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem,
      u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, a12, a9, a5, setw8, setw8, setw8,
      mov32_zero, csumMem, ← hcs]
  · intro r h₁ h₂
    rw [u₁₆.gpr, u₁₅.gpr, u₁₄.other _ h₁, u₁₃.gpr, u₁₂.other _ h₁, u₁₁.other _ h₁, u₁₀.gpr, u₉.other _ h₁,
      u₈.other _ h₁, u₇.other _ h₁, u₆.gpr, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₂,
      u₁.other _ h₂]
  · rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
      u₂.rd, u₁.rd]
  · rw [u₁₆.wr, u₁₅.wr, w14]

/-! ## The digits -/

theorem dsum_le (m : Mem) (S : Addr) : ∀ b, dsum m S b ≤ 30 * b
  | 0 => Nat.le_refl _
  | b + 1 => by
    have := dsum_le m S b
    have := (m (S + BitVec.ofNat 64 (Layout.oMsg + b))).isLt
    simp only [dsum, msgByte]; omega

/-- `Xmss.digits`: from the `n` bytes at `S + oMsg` (`r15`), their digits
and the checksum's to `S + oDigits`, and the frame's variables 0 and 1
zeroed (`csumMem` of `dmem`); only `rax`, `rcx`, `r10` and `r11` change. -/
theorem digits_ok (L : Layout) (hn : L.n ≤ 32) {s : State} {S : Addr} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h15 : s.gpr .r15 = S + BitVec.ofNat 64 Layout.oMsg)
    (hW : ∀ o, o + 8 ≤ 65536 → InRegions s.wr (S + BitVec.ofNat 64 o) 8)
    (hW1 : ∀ o, o + 1 ≤ 65536 → InRegions s.wr (S + BitVec.ofNat 64 o) 1)
    (hR1 : ∀ o, o + 1 ≤ 65536 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 o) 1)
    (k : ∀ s', s'.mem = csumMem (dmem s.mem S L.n) S L.n (15 * 2 * L.n - dsum s.mem S L.n) →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.X86_64.Xmss.digits L ++ is)) s Q := by
  simp only [Impl.SlhDsa.X86_64.Xmss.digits, Impl.SlhDsa.X86_64.Xmss.var, List.cons_append, List.append_assoc,
    List.range_eq_range']
  refine wp_mov32i fun s₁ u₁ => ?_
  refine bytes_ok L.n (by omega) s.mem S L.n 0 (by omega) (s := s₁) (by rw [u₁.mem]; rfl)
    (by rw [u₁.other _ (by decide), hbx]) (by rw [u₁.other _ (by decide), h15])
    (by rw [u₁.gpr]; rfl) (fun o ho => by rw [u₁.wr]; exact hW1 o ho)
    (fun o ho => by rw [u₁.rd, u₁.wr]; exact hR1 o ho) fun s₂ hm₂ h10₂ hk₂ hrd₂ hwr₂ => ?_
  have hb2 : s₂.gpr .rbx = S := by rw [hk₂ _ (by decide) (by decide) (by decide), u₁.other _ (by decide), hbx]
  refine tail_ok L (by omega) (by have := dsum_le s.mem S L.n; omega) hb2 h10₂
    (fun o ho => by rw [hwr₂, u₁.wr]; exact hW o ho) (fun o ho => by rw [hwr₂, u₁.wr]; exact hW1 o ho)
    fun s₃ hm₃ hk₃ hrd₃ hwr₃ => k s₃ (by rw [hm₃, hm₂]) (fun r h₁ h₂ h₃ h₄ => by
      rw [hk₃ r h₁ h₄, hk₂ r h₁ h₂ h₃, u₁.other _ h₃]) (by rw [hrd₃, hrd₂, u₁.rd]) (by rw [hwr₃, hwr₂, u₁.wr])

end VG.Proof.SlhDsa.X86_64
