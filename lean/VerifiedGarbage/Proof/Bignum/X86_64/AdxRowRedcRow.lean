import VerifiedGarbage.Impl.Bignum.X86_64.AdxRowRedc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

/-!
# Rows of eight-word blocks

`AdxRowRedc.row` adds `rdx` times the `w` words at `r9` to the `w` words at
`r8`, its carry into word `w` in `rcx` (`row_ok`, `AdxSquareWide.row_ok`'s
statement): a word (`word_ok`), a pair and a chain of them with both carries
live, a block with its chains closed into `rcx` (`block_ok`), and the blocks'
loop (`blocks_ok`) with `AdxSquare.RowInv`.
-/

namespace VG.Proof.Bignum.X86_64.AdxRowRedc

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.Bignum.X86_64.AdxRotate8 (ea_at)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem store_ok {s : State} {B : Addr} {Z e k : Nat} (hs : Scr s B Z)
    (h13 : s.gpr .r13 = off B e) (hZ : e + 8 * k + 8 ≤ Z) :
    WP isa (.block [.store (at_ .r13 (8 * k)) .r11]) s fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
  xrun [ea_at h13 (8 * k), hs.st hZ]

/-- Word `k`: the window's word plus `rdx` times the modulus's, the
previous high half and both carries, in the word and `hi`. -/
theorem word_ok {s : State} {B : Addr} {Z e eb k : Nat} {hi prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (h13 : s.gpr .r13 = off B e) (h15 : s.gpr .r15 = off B eb)
    (hZ : e + 8 * k + 8 ≤ Z) (hZb : eb + 8 * k + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o)
    (d1 : hi ≠ .r11) (d2 : prev ≠ hi) (d3 : prev ≠ .r11) (d4 : hi ≠ .r13) :
    WP isa (.block (AdxRowRedc.word k hi prev)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (word t.mem B (e + 8 * k)).toNat + 2 ^ 64 * ((t.gpr hi).toNat + c'.toNat + o'.toNat) =
        (word s.mem B (e + 8 * k)).toNat + (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * k)).toNat +
        (s.gpr prev).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * k) 8 s.mem t.mem ∧ Keep [hi, .r11] s t := by
  have hn := hs.nowrap
  rw [show AdxRowRedc.word k hi prev = ([.mulx hi .r11 (.mem (at_ .r15 (8 * k)))] : List Instr) ++
    (([.adcx .r11 (.mem (at_ .r13 (8 * k)))] : List Instr) ++ (([.adox .r11 (.reg prev)] : List Instr) ++
      ([.store (at_ .r13 (8 * k)) .r11] : List Instr))) from rfl, WP.block_append_iff]
  refine WP.mono (mulx_ok s (readSrc_word hs (ea_at h15 (8 * k)) hZb) (fun _ h => nomatch h) d1)
    fun s₁ ⟨e₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have ht₁ : readSrc s₁ (.mem (at_ .r13 (8 * k))) = some (word s.mem B (e + 8 * k)) := by
    rw [k₁.readMem (by simp [at_, Ne.symm d4]) (by simp [at_])]
    exact readSrc_word hs (ea_at h13 (8 * k)) hZ
  refine WP.mono (adcx_ok s₁ ht₁ (fun _ h => nomatch h) (c₁.trans hc)) fun s₂ ⟨c', hc₂, ho₂, e₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adox_ok s₂ (src := .reg prev) rfl (fun _ h => nomatch h) (ho₂.trans (o₁.trans ho)))
    fun s₃ ⟨o', ho₃, hc₃, e₃, k₃⟩ => ?_
  have k₁₃ := k₁.trans (k₂.trans k₃)
  have hs₃ : Scr s₃ B Z := hs.congr k₁₃.keep.2.2
  have h13₃ : s₃.gpr .r13 = off B e := (k₁₃.gpr (by simp [Ne.symm d4])).trans h13
  refine WP.mono (store_ok hs₃ h13₃ hZ) fun t ⟨hm, ct, ot, kt⟩ => ?_
  have p₂ : s₂.gpr prev = s.gpr prev := (k₂.gpr (by simpa using d3)).trans (k₁.gpr (by simp [d2, d3]))
  have h₃ : s₃.gpr hi = s₁.gpr hi := (k₃.gpr (by simpa using d1)).trans (k₂.gpr (by simpa using d1))
  have m₃ : s₃.mem = s.mem := k₁₃.2.1
  refine ⟨c', o', ct.trans (hc₃.trans hc₂), ot.trans ho₃, ?_, ?_, (k₁₃.keep.trans kt).mono (by simp)⟩
  · rw [kt.gpr (by simp), hm, word_writeW_self, h₃]
    rw [p₂] at e₃
    omega
  · rw [hm, m₃]; exact writeW_outside _ _ _ (by omega)

/-- Two words, the high half back in `rcx`. -/
theorem pair_ok {s : State} {B : Addr} {Z e eb k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h13 : s.gpr .r13 = off B e) (h15 : s.gpr .r15 = off B eb)
    (hZ : e + 8 * k + 16 ≤ Z) (hZb : eb + 8 * k + 16 ≤ Z)
    (sb : eb + 8 * k + 16 ≤ e + 8 * k ∨ e + 8 * k + 16 ≤ eb + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxRowRedc.pair k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * k) 2 + 2 ^ 128 * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * k) 2 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * k) 2 +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * k) 16 s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  have hn := hs.nowrap
  unfold AdxRowRedc.pair
  rw [WP.block_append_iff]
  refine WP.mono (word_ok hs h13 h15 (by omega) (by omega) hc ho
    (by decide) (by decide) (by decide) (by decide))
    fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
  refine WP.mono (word_ok (k := k + 1) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h13)
    ((ka.gpr (by decide)).trans h15) (by omega) (by omega) hca hoa
    (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
  have he : e + 8 * (k + 1) = e + 8 * k + 8 := by omega
  have heb : eb + 8 * (k + 1) = eb + 8 * k + 8 := by omega
  rw [he, heb, ka.gpr (by decide)] at et
  rw [he] at outt
  have lo : word t.mem B (e + 8 * k) = word a.mem B (e + 8 * k) := outt.word (by omega) (by omega)
  have ti : word a.mem B (e + 8 * k + 8) = word s.mem B (e + 8 * k + 8) := outa.word (by omega) (by omega)
  have bi : word a.mem B (eb + 8 * k + 8) = word s.mem B (eb + 8 * k + 8) := outa.word (by omega) (by omega)
  rw [ti, bi] at et
  refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
  · rw [AdxSquare.wv2, AdxSquare.wv2, AdxSquare.wv2, lo]
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (s.gpr .rdx).toNat]
    omega_using [ea, et]
  · exact (outa.mono (o' := e + 8 * k) (n' := 16) (Nat.le_refl _) (by omega)).trans
      (outt.mono (o' := e + 8 * k) (n' := 16) (by omega) (by omega))

/-- `n` pairs, with both carries live. -/
theorem chain_ok (n : Nat) {s : State} {B : Addr} {Z e eb k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h13 : s.gpr .r13 = off B e) (h15 : s.gpr .r15 = off B eb)
    (hZ : e + 8 * k + 8 * (2 * n) ≤ Z) (hZb : eb + 8 * k + 8 * (2 * n) ≤ Z)
    (sb : eb + 8 * k + 8 * (2 * n) ≤ e + 8 * k ∨ e + 8 * k + 8 * (2 * n) ≤ eb + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxRowRedc.chain n k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * k) (2 * n) + 2 ^ (64 * (2 * n)) * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * k) (2 * n) + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * k) (2 * n) +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * k) (8 * (2 * n)) s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  induction n generalizing s k c o with
  | zero =>
    apply WP.block_nil
    exact ⟨c, o, hc, ho, by simp [wv], Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    have hn := hs.nowrap
    rw [AdxRowRedc.chain, WP.block_append_iff]
    refine WP.mono (pair_ok hs h13 h15 (by omega) (by omega) (by omega) hc ho)
      fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
    refine WP.mono (ih (k := k + 2) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h13)
      ((ka.gpr (by decide)).trans h15) (by omega) (by omega) (by omega) hca hoa)
      fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
    have he : e + 8 * (k + 2) = e + 8 * k + 8 * 2 := by omega
    have heb : eb + 8 * (k + 2) = eb + 8 * k + 8 * 2 := by omega
    rw [he, heb, ka.gpr (by decide)] at et
    rw [he] at outt
    have lo : wv t.mem B (e + 8 * k) 2 = wv a.mem B (e + 8 * k) 2 := outt.wv (by omega) (by omega)
    have ti : wv a.mem B (e + 8 * k + 8 * 2) (2 * n) = wv s.mem B (e + 8 * k + 8 * 2) (2 * n) :=
      outa.wv (by omega) (by omega)
    have bi : wv a.mem B (eb + 8 * k + 8 * 2) (2 * n) = wv s.mem B (eb + 8 * k + 8 * 2) (2 * n) :=
      outa.wv (by omega) (by omega)
    rw [ti, bi] at et
    refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
    · rw [show 2 * (n + 1) = 2 + 2 * n by omega, wv_add, wv_add, wv_add, lo,
        show 64 * (2 + 2 * n) = 128 + 64 * (2 * n) by omega, Nat.pow_add]
      grind
    · exact (outa.mono (o' := e + 8 * k) (n' := 8 * (2 * (n + 1))) (Nat.le_refl _) (by omega)).trans
        (outt.mono (o' := e + 8 * k) (n' := 8 * (2 * (n + 1))) (by omega) (by omega))

theorem off_add_imm {B : Addr} {x : Nat} (d : Nat) :
    off B x + BitVec.ofNat 64 d = off B (x + d) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- A block: eight words, both chains closed into `rcx`, the pointers and the
count advanced, and ZF set when the count reaches `w`. -/
theorem block_ok {s : State} {B : Addr} {Z e eb j w : Nat}
    (hs : Scr s B Z) (h13 : s.gpr .r13 = off B (e + 8 * j)) (h15 : s.gpr .r15 = off B (eb + 8 * j))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hZ : e + 8 * j + 64 ≤ Z) (hZb : eb + 8 * j + 64 ≤ Z)
    (sb : eb + 8 * j + 64 ≤ e + 8 * j ∨ e + 8 * j + 64 ≤ eb + 8 * j)
    (hj : j + 8 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxRowRedc.block) s fun t =>
      wv t.mem B (e + 8 * j) 8 + 2 ^ 512 * (t.gpr .rcx).toNat =
        wv s.mem B (e + 8 * j) 8 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j) 8 + (s.gpr .rcx).toNat ∧
      Outside B (e + 8 * j) 64 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 8) ∧
      t.gpr .r13 = off B (e + 8 * (j + 8)) ∧ t.gpr .r15 = off B (eb + 8 * (j + 8)) ∧
      t.zf = some (decide (j + 8 = w)) ∧ Keep [.rsi, .rax, .r11, .rcx, .r14, .r13, .r15] s t := by
  unfold AdxRowRedc.block
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun a ⟨_, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok 4 (k := 0) (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans h13)
    ((ka.gpr (by decide)).trans h15) (by simpa using hZ) (by simpa using hZb) (by simpa using sb) ca oa)
    fun b ⟨cb, ob, hcb, hob, eq, out, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Bool.toNat_false, ka.2.1] at eq out
  rw [ka.gpr (r := .rdx) (by decide), ka.gpr (r := .rcx) (by decide)] at eq
  rw [WP.block_append_iff]
  refine WP.mono (close_ok b hcb hob (by decide)) fun d ⟨cd, od, _, _, ed, kd⟩ => ?_
  have hT := wv_lt s.mem B (e + 8 * j) 8
  have hB := wv_lt s.mem B (eb + 8 * j) 8
  simp only [Nat.reduceMul] at hT hB
  have hX := (s.gpr .rdx).isLt
  have hC := (s.gpr .rcx).isLt
  have hb : (b.gpr .rcx).toNat + cb.toNat + ob.toNat < 2 ^ 64 :=
    AdxSquareWide.carry_bound (R := 2 ^ 512) (V := wv b.mem B (e + 8 * j) 8)
      (T := wv s.mem B (e + 8 * j) 8) (X := (s.gpr .rdx).toNat)
      (Y := wv s.mem B (eb + 8 * j) 8) (C := (s.gpr .rcx).toNat)
      (Nat.two_pow_pos 512) hT hX hB hC eq
  have eclose : (d.gpr .rcx).toNat = (b.gpr .rcx).toNat + cb.toNat + ob.toNat := by
    have := Bool.toNat_le cd; have := Bool.toNat_le od
    omega_using [ed, hb, this]
  have k := (ka.keep.trans kb).trans kd.keep
  have h14d := (k.gpr (by decide)).trans h14
  have h13d := (k.gpr (by decide)).trans h13
  have h15d := (k.gpr (by decide)).trans h15
  have hbxd := (k.gpr (by decide)).trans hbx
  have tail : WP isa (.block [.alu .add .r13 (.imm 64), .alu .add .r15 (.imm 64), .alu .add .r14 (.imm 8),
      .alu .cmp .r14 (.reg .rbx)]) d fun t =>
      t.gpr .r14 = BitVec.ofNat 64 (j + 8) ∧ t.gpr .r13 = off B (e + 8 * (j + 8)) ∧
      t.gpr .r15 = off B (eb + 8 * (j + 8)) ∧ t.zf = some (decide (j + 8 = w)) ∧
      t.mem = d.mem ∧ Keep [.r13, .r15, .r14] d t := by
    refine WP.mono (WP.keep [.r13, .r15, .r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (j + 8) ∧
      t.gpr .r13 = off B (e + 8 * (j + 8)) ∧ t.gpr .r15 = off B (eb + 8 * (j + 8)) ∧
      t.zf = some (decide (j + 8 = w)) ∧ t.mem = d.mem) ?_ rfl)
      fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, kt⟩
    have ha : BitVec.ofNat 64 j + 8 = BitVec.ofNat 64 (j + 8) := by
      rw [BitVec.ofNat_add]; rfl
    have a13 : off B (e + 8 * j) + 64 = off B (e + 8 * (j + 8)) := by
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, off_add_imm]; congr 1
    have a15 : off B (eb + 8 * j) + 64 = off B (eb + 8 * (j + 8)) := by
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, off_add_imm]; congr 1
    xrun [h14d, h13d, h15d, hbxd, ha, a13, a15, ofNat_sub_beq hj hw]
    exact ⟨a13, a15⟩
  refine WP.mono tail fun t ⟨ht14, ht13, ht15, htz, hm, kt⟩ =>
    ⟨?_, ?_, ht14, ht13, ht15, htz, (k.trans kt).mono (by simp)⟩
  · rw [hm, kd.2.1, kt.gpr (by decide), eclose]; exact eq
  · rw [hm, kd.2.1]; exact out

/-- The loop of blocks, from any whole number of blocks done. -/
theorem blocks_ok {s₀ s : State} {B : Addr} {Z e eb a w : Nat}
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (h13 : s.gpr .r13 = off B (e + 8 * (8 * a)))
    (h15 : s.gpr .r15 = off B (eb + 8 * (8 * a)))
    (hw8 : w % 8 = 0) (haw : 8 * a < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb)
    (hI : AdxSquare.RowInv s₀ B Z e eb (8 * a) s) :
    WP isa (.loop (.block AdxRowRedc.block) .ne) s (AdxSquare.RowInv s₀ B Z e eb w) := by
  refine wp_upto (a := a) (N := w / 8) (by omega)
    (fun k t => AdxSquare.RowInv s₀ B Z e eb (8 * k) t ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.gpr .r13 = off B (e + 8 * (8 * k)) ∧ t.gpr .r15 = off B (eb + 8 * (8 * k))) ?_ ?_
    ⟨hI, hbx, h13, h15⟩
  · intro k _ hk t h
    obtain ⟨h, hbx', h13', h15'⟩ := h
    refine WP.mono (block_ok h.scr h13' h15' h.r14 hbx'
      (by omega) (by omega) (by omega) (by omega) (by omega))
      fun t' ⟨hv, ho, h14, ht13, ht15, hz, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans hbx', ?_, ?_⟩
    · exact hz.trans (congrArg some (decide_eq_decide.mpr (by omega_using [hk, hw8])))
    · have step := @AdxSquare.RowInv.step s₀ t t' B Z e eb (8 * k) 8 w h
        (by omega_using [hk, hw8] : 8 * k + 8 ≤ w) hZ hZb sb (by simpa only [Nat.reduceMul] using hv) ho h14
        (kt.mono (by decide))
      rw [show 8 * (k + 1) = 8 * k + 8 by omega_using []]
      exact step
    · rw [ht13]; congr 1
    · rw [ht15]; congr 1
  · intro t h
    have he : 8 * (w / 8) = w := by omega
    exact he ▸ h.1

/-- `AdxSquareWide.row_ok`'s statement, for `w` a positive multiple of 8. -/
theorem row_ok {s : State} {B : Addr} {Z e eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hw1 : 0 < w) (hw8 : w % 8 = 0) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) :
    WP isa AdxRowRedc.row s fun t =>
      wv t.mem B e w + 2 ^ (64 * w) * (t.gpr .rcx).toNat =
        wv s.mem B e w + (s.gpr .rdx).toNat * wv s.mem B eb w ∧
      Outside B e (8 * w) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 w ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t := by
  unfold AdxRowRedc.row
  have init : WP isa (.block AdxRowRedc.rowInit) s
      fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧ t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧
        t.gpr .r13 = off B e ∧ t.gpr .r15 = off B eb ∧
        t.mem = s.mem ∧ Keep [.rbx, .rcx, .r14, .r13, .r15] s t := by
    refine WP.mono (WP.keep [.rbx, .rcx, .r14, .r13, .r15] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧ t.gpr .r13 = off B e ∧ t.gpr .r15 = off B eb ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
    unfold AdxRowRedc.rowInit
    xrun [hbp, h8, h9]
  refine WP.seq (WP.mono init fun b ⟨hbx, hcx, h14, h13, h15, hmb, kb⟩ => ?_)
  have inv : AdxSquare.RowInv b B Z e eb 0 b :=
    ⟨hs.congr kb.2.2, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (blocks_ok (a := 0) hbx (by simpa using h13) (by simpa using h15) hw8 (by omega) hw
    hZ hZb sb inv)
    fun t hi => ⟨?_, ?_, hi.r14, (kb.trans hi.keep).mono (by decide)⟩
  · have hv := hi.val
    rw [hmb, kb.gpr (by decide), hcx] at hv
    simpa using hv
  · have ho := hi.out; rw [hmb] at ho; exact ho

end VG.Proof.Bignum.X86_64.AdxRowRedc
