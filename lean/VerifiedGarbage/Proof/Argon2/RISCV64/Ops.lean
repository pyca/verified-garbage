module

import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp

/-! # Argon2 on RISC-V: the derivation's arithmetic and logical instructions -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd WP.cons)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mul {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_mulhu {d n m : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q :=
  WP.cons exec_mulhu (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_srl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_lwu {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 4 = 0)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w ho (by rw [ha]; exact hal) (by rw [ha]; exact hin), ha]

theorem wp_sw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 4 = 0) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w ho (by rw [ha]; exact hal) (by rw [ha]; exact hout), ha]

theorem sext32_ushiftRight (x : BitVec 32) {sh : Nat} (h0 : 0 < sh) :
    sext32 (x >>> sh) = (x >>> sh).setWidth 64 := by
  refine BitVec.signExtend_eq_setWidth_of_msb_false ?_
  rw [BitVec.msb_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  have hp : 2 ≤ 2 ^ sh := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ sh := Nat.pow_le_pow_right (by omega) h0
  have : x.toNat / 2 ^ sh < 2 ^ 31 := Nat.div_lt_of_lt_mul (by omega)
  simpa using this

/-- `srliw` by a positive count: the low word shifted, zero-extended. -/
theorem wp_srlw {d n : Reg} {sh : Nat} (h : sh < 32) (h0 : 0 < sh)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 >>> sh).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .w d n sh :: is)) s Q := by
  refine WP.cons (exec_shift_w h) ?_
  simp only
  rw [sext32_ushiftRight _ h0]
  exact k _ (Upd.write _ _ _)

end


theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-- `s'` is `s` with (at most) the registers `ds` changed. -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.refl (ds : List Reg) (s : State) : Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr, u.sp⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr, h.sp⟩

end VG.Proof.Argon2.RISCV64
