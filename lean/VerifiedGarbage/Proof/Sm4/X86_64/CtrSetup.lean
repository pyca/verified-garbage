import VerifiedGarbage.Proof.Sm4.X86_64.CtrGroup

/-!
# SM4-CTR on x86-64: the counter block on entry

`ctrSetup_ok`: the counter block `T₁` at `rsi` (a number `V`, big-endian) to
the running counter's slots, as `hiOf V` and `loOf V`, and `T₁ + n` back to
`rsi`.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st at_)
open VG.Proof.Sm4 (ofInt_nat)
open VG.Spec.Aes (bytesAt)

/-- `mov d, [r + off]`. -/
theorem ld_ok (s : State) (d r : Reg) (off : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 off) 8) :
    ∃ s', runBlock isa [.mov d (.mem (at_ r off))] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 off) 64 ∧
      (∀ x, x ≠ d → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d (s.mem.readW (s.gpr r + BitVec.ofNat 64 off) 64), by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.ea, ofInt_nat, hr,
      ite_true, Option.map_some],
    RegUpd.gpr_setReg_self _ _ _, fun _ hx => RegUpd.gpr_setReg_of_ne _ _ hx, rfl, rfl, rfl⟩

/-- `mov [r + off], v`. -/
theorem stM_ok (s : State) (r v : Reg) (off : Nat) (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 off) 8) :
    ∃ s', runBlock isa [.store (at_ r off) v] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) (s.gpr v) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨{ s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) (s.gpr v) }, by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, State.ea, ofInt_nat, hw,
      ite_true], rfl, rfl, rfl, rfl⟩

theorem addN_vals (V N : Nat) (hN : N < 2 ^ 64) :
    loOf V + BitVec.ofNat 64 N = loOf (V + N) ∧
    hiOf V + (0 : BitVec 32).signExtend 64 +
        (BitVec.ofBool (decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 N).toNat))).setWidth 64 =
      hiOf (V + N) := by
  have e0 : ((0 : BitVec 32).signExtend 64) = BitVec.ofNat 64 0 := rfl
  refine ⟨by rw [loOf, loOf, BitVec.ofNat_add], ?_⟩
  rw [e0]
  apply BitVec.eq_of_toNat_eq
  simp only [hiOf, loOf, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  rw [Nat.mod_eq_of_lt hN]
  by_cases h : 2 ^ 64 ≤ V % 2 ^ 64 + N
  · rw [decide_eq_true h]
    simp only [Bool.toNat_true]
    have : (V + N) / 2 ^ 64 = V / 2 ^ 64 + 1 := by omega
    rw [this]; omega
  · rw [decide_eq_false h]
    simp only [Bool.toNat_false]
    have : (V + N) / 2 ^ 64 = V / 2 ^ 64 := by omega
    rw [this]; omega

/-- `add rbx, r8; adc rax, 0`: the running counter stepped by `r8`. -/
theorem addN_ok (s : State) {V N : Nat} (hN : N < 2 ^ 64) (hh : s.gpr .rax = hiOf V) (hl : s.gpr .rbx = loOf V)
    (hn : s.gpr .r8 = BitVec.ofNat 64 N) :
    ∃ s', runBlock isa [.alu .add .rbx (.reg .r8), .alu .adc .rax (.imm 0)] s = some s' ∧
      s'.gpr .rax = hiOf (V + N) ∧ s'.gpr .rbx = loOf (V + N) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨i1, i2⟩ := addN_vals V N hN
  let e1 := s.gpr .r8
  let e0 := (0 : BitVec 32).signExtend 64
  let c := decide (2 ^ 64 ≤ (s.gpr .rbx).toNat + e1.toNat)
  let s₁ := (arithFlags s (s.gpr .rbx + e1) c (addOverflow (s.gpr .rbx) e1 (s.gpr .rbx + e1))).setReg .rbx
    (s.gpr .rbx + e1)
  let r := s₁.gpr .rax + e0 + (BitVec.ofBool c).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (2 ^ 64 ≤ (s₁.gpr .rax).toNat + e0.toNat + c.toNat))
    (addOverflow (s₁.gpr .rax) e0 r)).setReg .rax r
  have g₁ : ∀ x, x ≠ .rbx → s₁.gpr x = s.gpr x := fun x hx => by
    simp only [s₁, RegUpd.gpr_setReg_of_ne _ _ hx, RegUpd.gpr_arithFlags]
  refine ⟨s₂, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.map_some]
    rfl
  · show s₁.gpr .rax + e0 + (BitVec.ofBool c).setWidth 64 = _
    rw [g₁ .rax (by decide), hh]
    simp only [c, e1, hl, hn]
    exact i2
  · show (s₂.gpr .rbx) = _
    simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ Reg.rax by decide), RegUpd.gpr_arithFlags, s₁,
      RegUpd.gpr_setReg_self, hl, e1, hn]
    exact i1
  · simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_arithFlags, g₁ _ h2]

/-- The counter block at `P`, as a number. -/
abbrev ctrVal (m : Mem) (P : Addr) : Nat := Spec.Ctr.toNat (bytesAt m P 16)

/-- Its halves are the byte-reversed words at `P` and `P + 8`. -/
theorem halves (m : Mem) (P : Addr) :
    hiOf (ctrVal m P) = bswap64 (m.readW P 64) ∧
      loOf (ctrVal m P) = bswap64 (m.readW (P + BitVec.ofNat 64 8) 64) := by
  have h := AesCtr.toNat_append (bytesAt m P 8) (bytesAt m (P + BitVec.ofNat 64 8) 8)
  rw [← AesCtr.bytesAt_append, AesCtr.bytesAt_rv64, AesCtr.bytesAt_rv64, AesCtr.toNat_ofNat, AesCtr.toNat_ofNat,
    AesCtr.length_ofNat] at h
  have a1 := (AesCtr.rv64 (m.readW P 64)).isLt
  have a2 := (AesCtr.rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).isLt
  simp only [Nat.reducePow] at a1 a2 h
  rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2] at h
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [hiOf, BitVec.toNat_ofNat, ctrVal, h, show bswap64 (m.readW P 64) = AesCtr.rv64 (m.readW P 64) from rfl]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [loOf, BitVec.toNat_ofNat, ctrVal, h,
      show bswap64 (m.readW (P + BitVec.ofNat 64 8) 64) = AesCtr.rv64 (m.readW (P + BitVec.ofNat 64 8) 64) from rfl]
    omega

/-- Slot `k` lies in the scratch buffer. -/
theorem slot_sub' {B : Addr} {k : Nat} (hk : k < slots) : Region.Sub ⟨wordAddr B k, 8⟩ ⟨B, 8 * slots⟩ :=
  VG.Offset.sub_base B (by have := slots_eq; omega)

/-- `bytesAt` of the two words written at `P + 8` and then `P`: the
big-endian bytes of `V`. -/
theorem bytes_pair2 (m : Mem) (P : Addr) (V : Nat) :
    bytesAt ((m.writeW (P + BitVec.ofNat 64 8) (bswap64 (loOf V))).writeW P (bswap64 (hiOf V))) P 16 =
      Spec.Ctr.ofNat V 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append,
    show (bswap64 (hiOf V)) = AesCtr.rv64 (hiOf V) from rfl, AesCtr.bytesAt_writeW_rv64,
    AesCtr.bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    show (bswap64 (loOf V)) = AesCtr.rv64 (loOf V) from rfl, AesCtr.bytesAt_writeW_rv64, AesCtr.ofNat_add]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [hiOf, BitVec.toNat_ofNat]; omega)
  · exact AesCtr.ofNat_congr (by simp only [loOf, BitVec.toNat_ofNat]; omega)

theorem ctrSetup_eq : ctrSetup =
    ([.mov .rax (.mem (at_ .rsi 0))] : List Instr) ++
      (([.bswap .rax] : List Instr) ++
      (([.mov .rbx (.mem (at_ .rsi 8))] : List Instr) ++
      (([.bswap .rbx] : List Instr) ++
      (([st ctrHi .rax] : List Instr) ++
      (([st ctrLo .rbx] : List Instr) ++
      (([.alu .add .rbx (.reg .r8), .alu .adc .rax (.imm 0)] : List Instr) ++
      (([.bswap .rax] : List Instr) ++
      (([.bswap .rbx] : List Instr) ++
      (([.store (at_ .rsi 8) .rbx] : List Instr) ++
      (([.store (at_ .rsi 0) .rax] : List Instr))))))))))) := rfl

/-- The counter block at `P` (`rsi`) to the running counter's slots, and the
block plus `N` (`r8`) back to `P`. -/
theorem ctrSetup_ok (s : State) {B P : Addr} {N : Nat} (hN : N < 2 ^ 64) (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr) (hP : s.gpr .rsi = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * slots⟩) (hn : s.gpr .r8 = BitVec.ofNat 64 N) :
    ∃ s', runBlock isa ctrSetup s = some s' ∧
      s'.mem.readW (wordAddr B ctrHi) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B ctrLo) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctrVal s.mem P + N) 16 ∧
      Frame [ctrRegion B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  have inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := ld_ok s .rax .rsi 0 (by rw [hP]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := bswap_ok s₁ .rax
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := ld_ok s₂ .rbx .rsi 8
    (by rw [rd₂, wr₂, rd₁, wr₁, o₂ _ (by decide), o₁ _ (by decide), hP]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := bswap_ok s₃ .rbx
  have g₄ : ∀ x, x ≠ .rax → x ≠ .rbx → s₄.gpr x = s.gpr x := fun x h1 h2 => by
    rw [o₄ x h2, o₃ x h2, o₂ x h1, o₁ x h1]
  have rax₄ : s₄.gpr .rax = hiOf V := by
    rw [o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hP, p0, hv]
  have rbx₄ : s₄.gpr .rbx = loOf V := by
    rw [r₄, r₃, m₂, m₁, o₂ _ (by decide), o₁ _ (by decide), hP, lv]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (b := B) (k := ctrHi) .rax
    (by rw [g₄ _ (by decide) (by decide), hB]) (by rw [wr₄']; exact slot_wr hw (by decide))
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stReg_ok (s := s₅) (b := B) (k := ctrLo) .rbx
    (by rw [g₅, g₄ _ (by decide) (by decide), hB]) (by rw [wr₅, wr₄']; exact slot_wr hw (by decide))
  obtain ⟨s₇, e₇, h₇, l₇, o₇, m₇, rd₇, wr₇⟩ := addN_ok s₆ (V := V) hN (by rw [g₆, g₅, rax₄])
    (by rw [g₆, g₅, rbx₄]) (by rw [g₆, g₅, g₄ _ (by decide) (by decide), hn])
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := bswap_ok s₇ .rax
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := bswap_ok s₈ .rbx
  have rsi₉ : s₉.gpr .rsi = P := by
    rw [o₉ _ (by decide), o₈ _ (by decide), o₇ _ (by decide) (by decide), g₆, g₅, g₄ _ (by decide) (by decide), hP]
  have wr₉' : s₉.wr = s.wr := by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄']
  obtain ⟨s₁₀, e₁₀, m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := stM_ok s₉ .rsi .rbx 8 (by rw [rsi₉, wr₉']; exact inP 8 (by decide))
  obtain ⟨s₁₁, e₁₁, m₁₁, g₁₁, rd₁₁, wr₁₁⟩ := stM_ok s₁₀ .rsi .rax 0
    (by rw [g₁₀, rsi₉, wr₁₀, wr₉']; exact inP 0 (by decide))
  have mem₆ : s₆.mem = (s.mem.writeW (wordAddr B ctrHi) (hiOf V)).writeW (wordAddr B ctrLo) (loOf V) := by
    rw [m₆, m₅, g₅, rax₄, rbx₄, m₄, m₃, m₂, m₁]
  have mem₁₁ : s₁₁.mem = (s₆.mem.writeW (P + BitVec.ofNat 64 8) (bswap64 (loOf (V + N)))).writeW P
      (bswap64 (hiOf (V + N))) := by
    rw [m₁₁, g₁₀, rsi₉, p0, m₁₀, rsi₉, m₉, m₈, m₇, o₉ .rax (by decide), r₈, h₇, r₉, o₈ .rbx (by decide), l₇]
  -- The frames.
  have fS : Frame [ctrRegion B] s.mem s₆.mem := by
    rw [mem₆]
    have hm : ctrRegion B ∈ [ctrRegion B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by decide) (by decide) (by decide))).writeW hm _
      (VG.Offset.contains B (by decide) (by decide) (by decide))
  have fP : Frame [⟨P, 16⟩] s₆.mem s₁₁.mem := by
    rw [mem₁₁]
    have hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have dP : ∀ k, k < slots → ∀ r ∈ [(⟨P, 16⟩ : Region)], Region.Disjoint ⟨wordAddr B k, 8⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hsep.sub_right (slot_sub' hk)).symm
  refine ⟨s₁₁, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, by rw [rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₁₁, wr₁₀, wr₉']⟩
  · rw [ctrSetup_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆,
      Option.bind_some, runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some, runBlock_app, e₉,
      Option.bind_some, runBlock_app, e₁₀, Option.bind_some, e₁₁]
  · rw [fP.readW (Region.contains_self _ _) (dP _ (by decide)) (by decide), mem₆,
      readW_slot_write _ (by decide) (by decide), ite_eq_right (by decide), Mem.readW_writeW_self64]
  · rw [fP.readW (Region.contains_self _ _) (dP _ (by decide)) (by decide), mem₆, Mem.readW_writeW_self64]
  · rw [mem₁₁]; exact bytes_pair2 _ _ _
  · exact (fS.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (fP.sub fun r hr => ⟨r, by
        simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  · rw [g₁₁, g₁₀, o₉ r h2, o₈ r h1, o₇ r h1 h2, g₆, g₅, g₄ r h1 h2]

end VG.Proof.Sm4.X86_64
