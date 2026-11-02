module

import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp

/-! # Argon2 on RISC-V: the derivation's arithmetic and logical instructions -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd WP.cons)

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
