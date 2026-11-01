module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Check
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ECDH and public keys over P-256 on RISC-V: the setup

The constants (`consts_ok`: `setConst` for each, apart), and what both
functions' setups share.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P256
open VG.Proof.X25519.RISCV64 (Rest)

/-- Constants to slots below 44, each its own. -/
theorem consts_ok : ∀ (L : List (Nat × Nat)) {s : State} {base : Addr}, WsReg s base → (∀ e ∈ L, e.1 < 44) →
    (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun e => setConst 4 (p256.sl e.1) e.2)) s fun s' =>
      Rest [.t0, .t1] s s' ∧ Unch base (L.map fun e => (p256.sl e.1, 32)) s.mem s'.mem ∧
      ∀ e ∈ L, sv base s' e.1 = e.2 % 2 ^ 256
  | [], s, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Unch.refl _ _ _, by simp⟩
  | (i, x) :: L, s, base, hw, hlt, hnd => by
    simp only [List.mem_cons, forall_eq_or_imp] at hlt
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (setConst_ok 4 hw (o := p256.sl i) (x := x) (by rw [sl_eq]; omega)
      (by rw [sl_eq]; omega)) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_)
    refine WP.mono (consts_ok L (hw.of_rest r₁) hlt.2 hnd.2) fun s₂ ⟨r₂, U₂, e₂⟩ => ⟨r₁.trans r₂, ?_, ?_⟩
    · exact O₁.unch.trans U₂
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · show wordsVal _ _ _ _ = _
        rw [U₂.wordsVal (fun w hw => by
          simp only [List.mem_map] at hw
          obtain ⟨e', he', rfl⟩ := hw
          have hne : e'.1 ≠ i := fun h => hnd.1 ⟨e', he', h⟩
          have := hlt.2 e' he'
          simp only [sl_eq]; omega) (by rw [sl_eq]; omega)]
        exact e₁
      · exact e₂ e he

/-- The constants, as `consts_ok` takes them. -/
theorem constCode_eq : constCode p256 = (consts p256).flatMap fun e => setConst 4 (p256.sl e.1) e.2 := rfl

/-- The constants' slots. -/
theorem consts_slots : ∀ e ∈ consts p256, e.1 < 44 := by decide

theorem consts_nodup : ((consts p256).map Prod.fst).Nodup := by decide

/-- The constants are below `2²⁵⁶`. -/
theorem consts_lt : ∀ e ∈ consts p256, e.2 < 2 ^ 256 := by decide

/-- `sd t, d(r)` at the working space's base, in `r`. -/
theorem sd_reg {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} {r : Reg} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0)
    {t : Reg} {d : Nat} (hd : d + 8 ≤ 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t r d :: is)) s Q :=
  wp_sd (by omega) (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    ⟨_, hwr, Offset.contains_base base (by omega) (by omega)⟩ k

/-- The saves, `s0 = r` and `s2 = a0`. -/
theorem save_ok {s : State} {r : Reg} {base : Addr} (h0 : s.gpr r = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hal : base.toNat % 8 = 0) :
    WP isa (.block (saveCode r)) s fun s' => WsReg s' base ∧ s'.gpr .s2 = s.gpr .a0 ∧
      (∀ x, x ≠ .s0 → x ≠ .s2 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Unch base [(0, 32)] s.mem s'.mem ∧
      word s'.mem base 0 = s.gpr .s0 ∧ word s'.mem base 8 = s.gpr .s1 ∧ word s'.mem base 16 = s.gpr .s2 ∧
      word s'.mem base 24 = s.gpr .ra := by
  rw [saveCode]
  refine sd_reg h0 hwr hal (d := 0) (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_reg (by rw [u₁.gpr]; exact h0) (by rw [u₁.wr]; exact hwr) hal (d := 8) (by decide) (by decide)
    fun s₂ u₂ => ?_
  refine sd_reg (by rw [u₂.gpr, u₁.gpr]; exact h0) (by rw [u₂.wr, u₁.wr]; exact hwr) hal (d := 16) (by decide)
    (by decide) fun s₃ u₃ => ?_
  refine sd_reg (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact h0) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hwr) hal (d := 24)
    (by decide) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have g₄ : ∀ x, s₄.gpr x = s.gpr x := fun x => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have m₄ : s₄.mem = (((s.mem.writeW (off base 0) (s.gpr .s0)).writeW (off base 8) (s.gpr .s1)).writeW
      (off base 16) (s.gpr .s2)).writeW (off base 24) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have O : ∀ {d} {m : Mem} {v : BitVec 64}, d ≤ 24 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun h => writeW_outside _ _ _ (by omega)
  have hw₆ : WsReg s₆ base := by
    refine ⟨by rw [u₆.other _ (by decide), u₅.gpr, g₄, h0], ?_, hn, hal⟩
    rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr
  have w0 : ∀ {d e} {m : Mem} {v : BitVec 64}, d ≤ 24 → e ≤ 24 → d + 8 ≤ e ∨ e + 8 ≤ d →
      word (m.writeW (off base e) v) base d = word m base d :=
    fun hd he h => (O he).word h (by omega)
  refine ⟨hw₆, by rw [u₆.gpr, u₅.other _ (by decide), g₄], fun x h1 h2 => by
      rw [u₆.other _ h2, u₅.other _ h1, g₄], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [m₆, m₄]
    exact ((((O (by decide)).unch.trans (O (by decide)).unch).trans (O (by decide)).unch).trans
      (O (by decide)).unch).cover (by decide)
  · rw [m₆, m₄, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide),
      w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₆, m₄, w0 (by decide) (by decide) (by decide), w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₆, m₄, w0 (by decide) (by decide) (by decide), word_writeW_self]
  · rw [m₆, m₄, word_writeW_self]

end VG.Proof.Ecdh.RISCV64.P256
