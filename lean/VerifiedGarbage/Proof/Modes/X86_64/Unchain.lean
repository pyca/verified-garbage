import VerifiedGarbage.Proof.Modes.X86_64.Copy
import VerifiedGarbage.Proof.Modes.Unchain

/-!
# Unchaining CBC blocks on x86-64

`unchainBlocks_wp`: the loop `unchainBlocks` turns `c ≥ 1` decrypted blocks
at `rax` (the core's buffer) and their ciphertext blocks at `rbx` (the data)
into the plaintext blocks: block `j` at `rbx` becomes the decrypted block
`j` XORed with the chaining value (the 16 bytes at `H`, the mode's
`hiSlot` and `loSlot`) for `j = 0`, and with ciphertext block `j - 1`
otherwise; the chaining value becomes the last ciphertext block. Each word's
stores are `Proof.Modes.unchainMem`'s.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st xorS)

/-! ## The instructions -/

/-- `mov d, [b + o]`. -/
theorem load_ok (s : State) (d b : Reg) (o : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.mov d (.mem (at_ b o))] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64 ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.ea, ofInt_nat, hr,
    ite_true, Option.map_some]

/-- `mov [b + o], r`. -/
theorem store_ok (s : State) (b r : Reg) (o : Nat) (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.store (at_ b o) r] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 o) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨{ s with mem := s.mem.writeW (s.gpr b + BitVec.ofNat 64 o) (s.gpr r) }, ?_, rfl, rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, State.ea, ofInt_nat, hw, ite_true]

/-- `xor d, [sb + 8 k]`. -/
theorem xorS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr b k) 8) :
    ∃ s', runBlock isa [xorS d k] s = some s' ∧ s'.gpr d = s.gpr d ^^^ s.mem.readW (wordAddr b k) 64 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr' : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * k)) 8 := hr
  refine ⟨(arithFlags s (s.gpr d ^^^ s.mem.readW (wordAddr b k) 64) false false).setReg d
    (s.gpr d ^^^ s.mem.readW (wordAddr b k) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩
  simp only [xorS, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, State.ea, ofInt_nat, hb, hr', ite_true, Option.bind_some, wordAddr]

variable {c : Core}

/-- `unchainWord w`, with the scratch buffer at `b`: `unchainMem` at the
words `8 w` from `rax` and `rbx` and the chaining value's word `w`. -/
theorem unchainWord_ok {s : State} {b : Addr} (w : Nat) (hb : s.gpr sb = b)
    (ha : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 (8 * w)) 8)
    (hh : InRegions s.wr (wordAddr b (c.hiSlot + w)) 8)
    (he : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (8 * w)) 8) :
    ∃ s', runBlock isa (c.unchainWord w) s = some s' ∧
      s'.mem = unchainMem s.mem (s.gpr .rax + BitVec.ofNat 64 (8 * w)) (wordAddr b (c.hiSlot + w))
        (s.gpr .rbx + BitVec.ofNat 64 (8 * w)) ∧
      (∀ r, r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let a := s.gpr .rax + BitVec.ofNat 64 (8 * w)
  let h := wordAddr b (c.hiSlot + w)
  let e := s.gpr .rbx + BitVec.ofNat 64 (8 * w)
  obtain ⟨s₁, e₁, d₁, o₁, m₁, rd₁, wr₁⟩ := load_ok s .rbp .rax (8 * w) (inRd ha)
  obtain ⟨s₂, e₂, d₂, o₂, m₂, rd₂, wr₂⟩ := xorS_ok (s := s₁) (k := c.hiSlot + w) .rbp
    (by rw [o₁ _ (by decide), hb]) (by rw [rd₁, wr₁]; exact inRd hh)
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := store_ok s₂ .rax .rbp (8 * w)
    (by rw [wr₂, wr₁, o₂ _ (by decide), o₁ _ (by decide)]; exact ha)
  obtain ⟨s₄, e₄, d₄, o₄, m₄, rd₄, wr₄⟩ := load_ok s₃ .rbp .rbx (8 * w)
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, g₃, o₂ _ (by decide), o₁ _ (by decide)]; exact inRd he)
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (k := c.hiSlot + w) .rbp
    (by rw [o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide), hb])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact hh)
  obtain ⟨s₆, e₆, d₆, o₆, m₆, rd₆, wr₆⟩ := load_ok s₅ .rbp .rax (8 * w)
    (by rw [rd₅, wr₅, rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, g₅, o₄ _ (by decide), g₃, o₂ _ (by decide),
      o₁ _ (by decide)]; exact inRd ha)
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := store_ok s₆ .rbx .rbp (8 * w)
    (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, o₆ _ (by decide), g₅, o₄ _ (by decide), g₃, o₂ _ (by decide),
      o₁ _ (by decide)]; exact he)
  have rax₆ : s₆.gpr .rax = s.gpr .rax := by
    rw [o₆ _ (by decide), g₅, o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide)]
  have rbx₆ : s₆.gpr .rbx = s.gpr .rbx := by
    rw [o₆ _ (by decide), g₅, o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide)]
  refine ⟨s₇, ?_, ?_, fun r hr => ?_, by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · simp only [Core.unchainWord]
    rw [show ([.mov .rbp (.mem (at_ .rax (8 * w))), xorS .rbp (c.hiSlot + w), .store (at_ .rax (8 * w)) .rbp,
        .mov .rbp (.mem (at_ .rbx (8 * w))), st (c.hiSlot + w) .rbp, .mov .rbp (.mem (at_ .rax (8 * w))),
        .store (at_ .rbx (8 * w)) .rbp] : List Instr) =
        [.mov .rbp (.mem (at_ .rax (8 * w)))] ++ ([xorS .rbp (c.hiSlot + w)] ++
        ([.store (at_ .rax (8 * w)) .rbp] ++ ([.mov .rbp (.mem (at_ .rbx (8 * w)))] ++ ([st (c.hiSlot + w) .rbp] ++
        ([.mov .rbp (.mem (at_ .rax (8 * w)))] ++ ([.store (at_ .rbx (8 * w)) .rbp] : List Instr)))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  · have rax₄ : s₄.gpr .rax = s.gpr .rax := by rw [o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide)]
    have rbx₂ : s₂.gpr .rbx = s.gpr .rbx := by rw [o₂ _ (by decide), o₁ _ (by decide)]
    have rax₂ : s₂.gpr .rax = s.gpr .rax := by rw [o₂ _ (by decide), o₁ _ (by decide)]
    simp only [m₇, m₆, m₅, m₄, m₃, m₂, m₁, d₆, d₄, d₂, d₁, g₅, g₃, rbx₆, rax₄, rax₂, rbx₂, unchainMem]
  · rw [g₇, o₆ r hr, g₅, o₄ r hr, g₃, o₂ r hr, o₁ r hr]

/-! ## The loop -/

/-- Unchaining, after `j` of `nb` blocks: the decryptions at `A`, the
ciphertexts at `E`, the chaining value at `H`. -/
structure UInv (A E H : Addr) (nb : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = A + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = E + BitVec.ofNat 64 (16 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb - j)
  out : ∀ t < 16 * j, s.mem (E + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) ^^^
    (if t < 16 then s₀.mem (H + BitVec.ofNat 64 t) else s₀.mem (E + BitVec.ofNat 64 (t - 16)))
  rest : ∀ t, 16 * j ≤ t → t < 16 * nb → s.mem (E + BitVec.ofNat 64 t) = s₀.mem (E + BitVec.ofNat 64 t)
  bufRest : ∀ t, 16 * j ≤ t → t < 16 * nb → s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  chain : ∀ u < 16, s.mem (H + BitVec.ofNat 64 u) =
    if j = 0 then s₀.mem (H + BitVec.ofNat 64 u) else s₀.mem (E + BitVec.ofNat 64 (16 * (j - 1) + u))
  frame : Frame [⟨A, 16 * nb⟩, ⟨E, 16 * nb⟩, ⟨H, 16⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem UInv.init {A E H : Addr} {nb : Nat} {s₀ : State} (ha : s₀.gpr .rax = A) (hb : s₀.gpr .rbx = E)
    (hc : s₀.gpr .rcx = BitVec.ofNat 64 nb) : UInv A E H nb s₀ 0 s₀ :=
  ⟨by rw [ha]; simp, by rw [hb]; simp, by rw [hc, Nat.sub_zero], fun t ht => by omega, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ => by rw [ite_eq_left rfl], Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl⟩

theorem unchainBlocks_wp {B A E : Addr} {nb : Nat} {s₀ : State} (hn : 0 < nb)
    (hn59 : nb < 2 ^ 59) (hB : s₀.gpr sb = B)
    (inA : ∀ t < 2 * nb, InRegions s₀.wr (A + BitVec.ofNat 64 (8 * t)) 8)
    (inE : ∀ t < 2 * nb, InRegions s₀.wr (E + BitVec.ofNat 64 (8 * t)) 8)
    (inH : ∀ w < 2, InRegions s₀.wr (wordAddr B (c.hiSlot + w)) 8)
    (dAE : Region.Disjoint ⟨A, 16 * nb⟩ ⟨E, 16 * nb⟩) (dAH : Region.Disjoint ⟨A, 16 * nb⟩ ⟨wordAddr B c.hiSlot, 16⟩)
    (dEH : Region.Disjoint ⟨E, 16 * nb⟩ ⟨wordAddr B c.hiSlot, 16⟩)
    (hs : UInv A E (wordAddr B c.hiSlot) nb s₀ 0 s₀) :
    WP isa c.unchainBlocks s₀ (UInv A E (wordAddr B c.hiSlot) nb s₀ nb) := by
  let H := wordAddr B c.hiSlot
  have hH8 : wordAddr B (c.hiSlot + 1) = H + BitVec.ofNat 64 8 := by
    simp only [H, wordAddr]; rw [addr_add, Nat.mul_succ]
  have hN : 16 * nb < 2 ^ 64 := by omega
  have dHE : Region.Disjoint ⟨H, 16⟩ ⟨E, 16 * nb⟩ := fun y h1 h2 => dEH y h2 h1
  have dHA : Region.Disjoint ⟨H, 16⟩ ⟨A, 16 * nb⟩ := fun y h1 h2 => dAH y h2 h1
  have dEA : Region.Disjoint ⟨E, 16 * nb⟩ ⟨A, 16 * nb⟩ := fun y h1 h2 => dAE y h2 h1
  refine WP.loop (M := isa) (fun n s => ∃ j, n = nb - j ∧ j < nb ∧ UInv A E H nb s₀ j s)
    (fun n s hs => ?_) nb s₀ ⟨0, by omega, hn, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  let a := A + BitVec.ofNat 64 (16 * j)
  let e := E + BitVec.ofNat 64 (16 * j)
  have subA : Region.Sub ⟨a, 16⟩ ⟨A, 16 * nb⟩ := VG.Offset.sub_base A (by omega)
  have subE : Region.Sub ⟨e, 16⟩ ⟨E, 16 * nb⟩ := VG.Offset.sub_base E (by omega)
  have hah : Region.Disjoint ⟨a, 16⟩ ⟨H, 16⟩ := dAH.sub_left subA
  have hae : Region.Disjoint ⟨a, 16⟩ ⟨e, 16⟩ := (dAE.sub_left subA).sub_right subE
  have hhe : Region.Disjoint ⟨H, 16⟩ ⟨e, 16⟩ := dHE.sub_right subE
  have base : s.gpr sb = B := by rw [hi.regs _ (by decide) (by decide) (by decide) (by decide), hB]
  have wA : ∀ k, k < 2 → InRegions s.wr (a + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
    rw [hi.wr, addr_add, show 16 * j + 8 * k = 8 * (2 * j + k) by omega]; exact inA _ (by omega)
  have wE : ∀ k, k < 2 → InRegions s.wr (e + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
    rw [hi.wr, addr_add, show 16 * j + 8 * k = 8 * (2 * j + k) by omega]; exact inE _ (by omega)
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := unchainWord_ok (c := c) (s := s) 0 base
    (by rw [hi.rax]; exact wA 0 (by decide)) (by rw [hi.wr]; exact inH 0 (by decide))
    (by rw [hi.rbx]; exact wE 0 (by decide))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := unchainWord_ok (c := c) (s := s₁) 1
    (by rw [g₁ _ (by decide), base])
    (by rw [wr₁, g₁ _ (by decide), hi.rax]; exact wA 1 (by decide)) (by rw [wr₁, hi.wr]; exact inH 1 (by decide))
    (by rw [wr₁, g₁ _ (by decide), hi.rbx]; exact wE 1 (by decide))
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rax 16
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rbx 16
  obtain ⟨s₅, e₅, c₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rcx 1
  refine WP.of_runBlock ⟨s₅, by
    rw [show c.unchainWord 0 ++ c.unchainWord 1 ++
        ([.alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr) =
        c.unchainWord 0 ++ (c.unchainWord 1 ++ ([.alu .add .rax (.imm 16)] ++
        ([.alu .add .rbx (.imm 16)] ++ ([.alu .sub .rcx (.imm 1)] : List Instr)))) by simp,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have hm : s₅.mem = unchainMem (unchainMem s.mem a H e) (a + BitVec.ofNat 64 8) (H + BitVec.ofNat 64 8)
      (e + BitVec.ofNat 64 8) := by
    rw [m₅, m₄, m₃, m₂, m₁, g₁ _ (by decide), g₁ _ (by decide), hi.rax, hi.rbx, ← hH8]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, BitVec.add_zero, a, e, H]
  have ub := fun x => unchainBlock_apply s.mem x hah hae hhe
  -- Where the bytes of each region are.
  have eE : ∀ {t}, 16 * j ≤ t → t < 16 * (j + 1) → (E + BitVec.ofNat 64 t - e).toNat = t - 16 * j :=
    fun h1 h2 => off_sub_toNat E h1 (by omega)
  have nE : ∀ {t}, t < 16 * j ∨ 16 * (j + 1) ≤ t → t < 16 * nb → ¬ (E + BitVec.ofNat 64 t - e).toNat < 16 :=
    fun h1 h2 => off_sub_not E (by omega) (by omega) (by omega) (by omega)
  have nA : ∀ {t}, t < 16 * j ∨ 16 * (j + 1) ≤ t → t < 16 * nb → ¬ (A + BitVec.ofNat 64 t - a).toNat < 16 :=
    fun h1 h2 => off_sub_not A (by omega) (by omega) (by omega) (by omega)
  have EH : ∀ {t}, t < 16 * nb → ¬ (E + BitVec.ofNat 64 t - H).toNat < 16 :=
    fun h => not_near dEH h (by decide) (by omega)
  have Ea : ∀ {t}, t < 16 * nb → ¬ (E + BitVec.ofNat 64 t - a).toNat < 16 :=
    fun h => not_near (dEA.sub_right subA) h (by decide) (by omega)
  have Ae : ∀ {t}, t < 16 * nb → ¬ (A + BitVec.ofNat 64 t - e).toNat < 16 :=
    fun h => not_near (dAE.sub_right subE) h (by decide) (by omega)
  have AH : ∀ {t}, t < 16 * nb → ¬ (A + BitVec.ofNat 64 t - H).toNat < 16 :=
    fun h => not_near dAH h (by decide) (by omega)
  have hinv : UInv A E H nb s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun u hu => ?_,
      hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), g₁ _ (by decide), hi.rax,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rbx,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
        show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega),
        show nb - j - 1 = nb - (j + 1) by omega]
    · rw [hm, ub]
      by_cases h0 : 16 * j ≤ t
      · rw [ite_eq_left (by rw [eE h0 ht]; omega), eE h0 ht, addr_add A,
          show 16 * j + (t - 16 * j) = t by omega, hi.bufRest t (by omega) (by omega),
          hi.chain _ (by omega)]
        by_cases hj0 : j = 0
        · subst hj0
          rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.sub_zero]
        · rw [ite_eq_right hj0, ite_eq_right (by omega), show 16 * (j - 1) + (t - 16 * j) = t - 16 by omega]
      · rw [ite_eq_right (nE (.inl (by omega)) (by omega)), ite_eq_right (EH (by omega)),
          ite_eq_right (Ea (by omega))]
        exact hi.out t (by omega)
    · rw [hm, ub, ite_eq_right (nE (.inr h1) h2), ite_eq_right (EH h2), ite_eq_right (Ea h2)]
      exact hi.rest t (by omega) h2
    · rw [hm, ub, ite_eq_right (Ae h2), ite_eq_right (AH h2), ite_eq_right (nA (.inr h1) h2)]
      exact hi.bufRest t (by omega) h2
    · rw [hm, ub, ite_eq_right (not_near (dHE.sub_right subE) hu (Nat.le_refl _) (by decide)),
        ite_eq_left (by rw [off_self H (by omega)]; exact hu), off_self H (by omega), addr_add E, hi.rest _ (by omega) (by omega), ite_eq_right (by omega),
        show j + 1 - 1 = j by omega]
    · have hx1 : ¬ (x - e).toNat < 16 := fun h => hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
        (subE x (by simp only [Region.Contains]; omega))
      have hx2 : ¬ (x - H).toNat < 16 := fun h => hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)) (by simp only [Region.Contains]; omega)
      have hx3 : ¬ (x - a).toNat < 16 := fun h => hx _ List.mem_cons_self
        (subA x (by simp only [Region.Contains]; omega))
      rw [hm, ub, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hx3]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₅.zf = some (decide (nb - (j + 1) = 0)) := by
    rw [z₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  by_cases hl : j + 1 = nb
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show j + 1 = nb from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega, nb - (j + 1), by omega, j + 1, rfl, by omega, hinv⟩

end VG.Proof.Modes.X86_64
