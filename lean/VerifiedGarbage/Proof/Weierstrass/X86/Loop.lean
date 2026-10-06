import VerifiedGarbage.Proof.Weierstrass.X86.Copy

/-!
# Short Weierstrass curves on x86 (32-bit): loops counted down in `esi`

The ladder, the powers and the tables of bits loop with `esi` counting down:
the body starts with `sub esi, 1` (`decCounter_ok`) and ends with
`test esi, esi` (`testCounter_ok`), and the loop runs while `esi ≠ 0`
(`jne`). `countLoop_ok` runs such a loop `n ≥ 1` times from an invariant
indexed by `esi`. Also the byte loads and stores of the tables.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86 VG.Impl.Mont.X86 VG.Proof.Mont.X86 VG.Proof.Mont

/-- A loop whose body takes the invariant from `j` to `j - 1` and leaves
`ZF` set iff `j - 1 = 0`, run from `n ≥ 1`. -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.zf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by simp only [eval, hz, hj, decide_true, Option.map_some, Bool.not_true],
      hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false hj, Option.map_some, Bool.not_false],
      j - 1, by omega, by omega, by omega, hi'⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `esi -= 1`. -/
theorem wp_decCounter {j : Nat} (hj : 1 ≤ j) (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (k : ∀ t, t.gpr .esi = BitVec.ofNat 32 (j - 1) → Keeps [.esi] s t → t.mem = s.mem →
      WP isa (.block is) t Q) :
    WP isa (.block (decCounter :: is)) s Q :=
  wp_subS rfl fun t u _ => k t (by rw [u.gpr, hb]; exact ofNat_pred hj) u.keeps u.mem

/-- `test esi, esi`. -/
theorem wp_testCounter {j : Nat} (hj : j < 2 ^ 32) (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (k : ∀ t, Fupd s t → t.zf = some (decide (j = 0)) → WP isa (.block is) t Q) :
    WP isa (.block (testCounter :: is)) s Q :=
  wp_test fun t f z => k t f (by rw [z, hb, BitVec.and_self, ofNat_beq_zero hj])

/-- `movzx d, byte [m]`. -/
theorem wp_load8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hr : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  cons (by simp only [exec, ha, State.load8, hr, ite_true, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- `mov byte [m], r`. -/
theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)})
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- `[r + d]` where `r = edi + k`, in the working space. -/
theorem _root_.VG.Proof.Mont.X86.Scr.ea_reg {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r : Reg} {k d : Nat}
    (hr : s.gpr r = s.gpr .edi + BitVec.ofNat 32 k) (hd : k + d < size) :
    s.ea (at_ r d) = off base (k + d) := by
  change ((s.gpr r + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hr, Offset.add_add]
  exact hs.ea hd

end VG.Proof.Weierstrass.X86
