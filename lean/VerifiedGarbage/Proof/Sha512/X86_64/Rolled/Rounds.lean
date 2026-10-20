module

public import VerifiedGarbage.Proof.Sha512.X86_64.Compress
public import VerifiedGarbage.Impl.Sha512.X86_64.Rolled
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# SHA-512 on x86-64, rolled: a round, and `Kₜ` from the table

`Rolled.round t k` is round `t` when `k` addresses `Kₜ` in the table, the
base register holding the table's address (`exec_kSlot0`, `exec_kSlot`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Rolled

open VG VG.X86_64 VG.Impl.Sha512.X86_64 VG.Impl.Sha512.X86_64.Rolled
open VG.Proof.Sha512.X86_64 (Vars pubRegs var_succ var_succ_zero var_not_pub pubRegs_ne round_nodup
  ofInt_natCast)
open VG.Spec.Sha512 (HashValue Word Block K W)

/-- The index of iteration `j`. -/
abbrev idx (j : Nat) : BitVec 64 := BitVec.ofNat 64 (128 * j)

theorem Ks_length : Spec.Sha512.Ks.length = 80 := rfl

/-- Round `t < 16` reads `Kₜ`. -/
theorem exec_kSlot0 (s : State) (h : Reg) {t : Nat} (ht : t < 16) (hb : s.gpr .rsi = s.syms kSym) :
    X86_64.exec (.aluTbl .add h (kSlot0 t) kSym Spec.Sha512.Ks) s = execAluW .add h (K t) s := by
  have e : s.ea (kSlot0 t) - s.syms kSym = BitVec.ofNat 64 (8 * t) := by
    simp only [State.ea, kSlot0, ofInt_natCast]
    rw [hb, BitVec.add_comm, BitVec.add_sub_cancel]
  have e' : (BitVec.ofNat 64 (8 * t)).toNat = 8 * t := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : t < Spec.Sha512.Ks.length := by rw [Ks_length]; omega
  simp only [X86_64.exec, e, e', show (kSlot0 t).base = .rsi from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right t (by decide : 0 < 8), hl, and_self, ↓reduceIte]
  rfl

theorem kSlot_ea (s : State) {j : Nat} (h : s.gpr .rdx = idx j) (t' : Nat) :
    s.ea (kSlot t') = s.gpr .rsi + BitVec.ofNat 64 (8 * (16 * j + t')) := by
  simp only [State.ea, kSlot, h, ofInt_natCast, BitVec.mul_one]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 128 * j + 8 * t' = 8 * (16 * j + t') by omega]

/-- Round `16 j + t'` of iteration `j` reads `K (16 j + t')`. -/
theorem exec_kSlot (s : State) (h : Reg) {j : Nat} (t' : Nat) (hrdx : s.gpr .rdx = idx j)
    (hb : s.gpr .rsi = s.syms kSym) (hn : 16 * j + t' < 80) :
    X86_64.exec (.aluTbl .add h (kSlot t') kSym Spec.Sha512.Ks) s = execAluW .add h (K (16 * j + t')) s := by
  have e : s.ea (kSlot t') - s.syms kSym = BitVec.ofNat 64 (8 * (16 * j + t')) := by
    rw [kSlot_ea s hrdx, hb, BitVec.add_comm, BitVec.add_sub_cancel]
  have e' : (BitVec.ofNat 64 (8 * (16 * j + t'))).toNat = 8 * (16 * j + t') := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : 16 * j + t' < Spec.Sha512.Ks.length := by rw [Ks_length]; exact hn
  simp only [X86_64.exec, e, e', show (kSlot t').base = .rsi from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right (16 * j + t') (by decide : 0 < 8), hl, and_self, ↓reduceIte]
  rfl

/-- `T₁` as the round adds it, `Kₜ` and `Wₜ` first, in `a'`. -/
theorem t1_order (h k w s c r : Word) :
    h + (k + (w + (s + (c + r)))) = h + (s + (c + (k + (w + r)))) := by
  ac_rfl

/-- `T₁` as the round adds it, `Kₜ` and `Wₜ` first, in `e'`. -/
theorem t1_order' (d h k w s c : Word) :
    d + (h + (k + (w + (s + c)))) = d + (h + (s + (c + (k + w)))) := by
  ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`,
given what its read of the table adds. -/
theorem round_ok (t : Nat) (k : MemOp) (s : State) (v : HashValue) (kv w : Word)
    (hv : Vars t s v) (hk : X86_64.exec (.aluTbl .add (var t 7) k kSym Spec.Sha512.Ks) s =
      execAluW .add (var t 7) kv s) (hw : s.gpr T0 = w) :
    WP isa (.block (Rolled.round t k)) s fun s' =>
      Vars (t + 1) s' (roundKW v kv w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  have p3 := var_not_pub t 3
  have p7 := var_not_pub t 7
  apply WP.of_runBlock
  rw [show Rolled.round t k = .aluTbl .add (var t 7) k kSym Spec.Sha512.Ks :: (Rolled.round t k).tail
    from rfl, runBlock_cons, hk]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [Rolled.round, List.tail_cons]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' hw ⊢
  simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execAluW, execShift, readSrc,
    isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, hd, hd',
    h0, h1, h2, h3, h4, h5, h6, h7, hw,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · obtain ⟨-, n1, n2⟩ := pubRegs_ne hr
    have nh : r ≠ h := fun e => p7 (e ▸ hr)
    have nd : r ≠ d := fun e => p3 (e ▸ hr)
    simp only [T1, T2] at n1 n2
    simp only [nh, nd, n1, n2, ite_false]
  all_goals
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6,
      roundKW_7, bsig1_eq, ch_eq, bsig0_eq, maj_eq, BitVec.add_assoc]
  · exact t1_order _ _ _ _ _ _
  · exact t1_order' _ _ _ _ _ _

end VG.Proof.Sha512.X86_64.Rolled
