module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-512 with AVX-512VL on x86-64: two compressions at once

`Impl.Sha512.X86_64.Avx512.compress2`: each `xmm` register holds a value of
the first compression in quadword 0 and of the second in quadword 1, and
every instruction of a round acts on the two alike.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx512
open VG.Proof.Sha512.X86_64.Avx2 (qword_append_0 qword_append_1 paddq_eq psrlq_eq)
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj)
open VG.Proof.Sha512.X86_64 (ofInt_natCast)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq roundKW_0 roundKW_1 roundKW_2 roundKW_3 roundKW_4 roundKW_5
  roundKW_6 roundKW_7)

/-! ## `vpternlogd`, on quadwords -/

/-- `0xCA`: the bits of the second where the first has a one, of the third
where it has a zero. -/
theorem ternCA (a b c : BitVec 128) : ternlog a b c 0xCA = (a &&& b) ^^^ (~~~a &&& c) := by
  simp only [ternlog, List.range, List.range.loop, List.foldl,
    show (0xCA : BitVec 8).getLsbD 0 = false from rfl, show (0xCA : BitVec 8).getLsbD 1 = true from rfl,
    show (0xCA : BitVec 8).getLsbD 2 = false from rfl, show (0xCA : BitVec 8).getLsbD 3 = true from rfl,
    show (0xCA : BitVec 8).getLsbD 4 = false from rfl, show (0xCA : BitVec 8).getLsbD 5 = false from rfl,
    show (0xCA : BitVec 8).getLsbD 6 = true from rfl, show (0xCA : BitVec 8).getLsbD 7 = true from rfl,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj, decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

/-- `0xE8`: the majority. -/
theorem ternE8 (a b c : BitVec 128) : ternlog a b c 0xE8 = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
  simp only [ternlog, List.range, List.range.loop, List.foldl,
    show (0xE8 : BitVec 8).getLsbD 0 = false from rfl, show (0xE8 : BitVec 8).getLsbD 1 = false from rfl,
    show (0xE8 : BitVec 8).getLsbD 2 = false from rfl, show (0xE8 : BitVec 8).getLsbD 3 = true from rfl,
    show (0xE8 : BitVec 8).getLsbD 4 = false from rfl, show (0xE8 : BitVec 8).getLsbD 5 = true from rfl,
    show (0xE8 : BitVec 8).getLsbD 6 = true from rfl, show (0xE8 : BitVec 8).getLsbD 7 = true from rfl,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj, decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem ternCA_eq (a b c d e f : Word) :
    ternlog (a ++ b) (c ++ d) (e ++ f) 0xCA = ch a c e ++ ch b d f := by
  rw [ternCA, BitVec.and_append, BitVec.not_append, BitVec.and_append, BitVec.xor_append]; rfl

theorem ternE8_eq (a b c d e f : Word) :
    ternlog (a ++ b) (c ++ d) (e ++ f) 0xE8 = maj a c e ++ maj b d f := by
  rw [ternE8, BitVec.and_append, BitVec.and_append, BitVec.and_append, BitVec.xor_append, BitVec.xor_append]; rfl

/-! ## A round -/

/-- The working variables of both compressions, `v₀` and `v₁`, are in the
registers of round `t`. -/
def Vars2 (t : Nat) (s : State) (v₀ v₁ : HashValue) : Prop :=
  s.xmm (sv t 0) = v₁[0] ++ v₀[0] ∧ s.xmm (sv t 1) = v₁[1] ++ v₀[1] ∧ s.xmm (sv t 2) = v₁[2] ++ v₀[2] ∧
  s.xmm (sv t 3) = v₁[3] ++ v₀[3] ∧ s.xmm (sv t 4) = v₁[4] ++ v₀[4] ∧ s.xmm (sv t 5) = v₁[5] ++ v₀[5] ∧
  s.xmm (sv t 6) = v₁[6] ++ v₀[6] ∧ s.xmm (sv t 7) = v₁[7] ++ v₀[7]

theorem sv_succ (t k : Nat) (hk : k < 7) : sv (t + 1) (k + 1) = sv t k := by
  simp only [sv]; congr 1; omega

theorem sv_succ_zero (t : Nat) : sv (t + 1) 0 = sv t 7 := by
  simp only [sv]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round2_nodup (t : Nat) :
    [sv t 0, sv t 1, sv t 2, sv t 3, sv t 4, sv t 5, sv t 6, sv t 7, u0, u1, u2, w0, w1, mB].Nodup := by
  simp only [sv]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

/-- What a round leaves alone: all but the working variables and its
temporaries. -/
def Keeps2 (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr = s.gpr ∧
    (∀ r, r = w0 ∨ r = w1 ∨ r = mB → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r)

/-- `T₁`, as the round adds it up. -/
theorem t1_order2 (h e f g k w : Word) :
    h + (w + k) + ((e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) + ch e f g) =
      h + bsig1 e + ch e f g + k + w := by
  rw [show bsig1 e = e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41 from rfl]; ac_rfl

/-- `T₁ + T₂`, as the round adds it up. -/
theorem t2_order2 (t a b c : Word) :
    t + (a.rotateRight 28 ^^^ a.rotateRight 34 ^^^ a.rotateRight 39) + maj a b c = t + (bsig0 a + maj a b c) := by
  rw [BitVec.add_assoc]; rfl

/-- The round is symbolically executed once, for any registers `a … h`,
with `Wₜ + Kₜ` of both in `kw`. -/
theorem round2_ok (t : Nat) (kw : XReg) (hkw : kw = w0 ∨ kw = w1) (s : State) (v₀ v₁ : HashValue)
    (k x₀ x₁ : Word) (hv : Vars2 t s v₀ v₁) (hx : s.xmm kw = (x₁ + k) ++ (x₀ + k)) :
    WP isa (.block (round2 t kw)) s fun s' =>
      Vars2 (t + 1) s' (roundKW v₀ k x₀) (roundKW v₁ k x₁) ∧ Keeps2 s s' := by
  unfold Keeps2
  have hd := round2_nodup t
  have hd' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [Vars2, sv_succ_zero, sv_succ t _ (show 0 < 7 by omega),
    sv_succ t _ (show 1 < 7 by omega), sv_succ t _ (show 2 < 7 by omega),
    sv_succ t _ (show 3 < 7 by omega), sv_succ t _ (show 4 < 7 by omega),
    sv_succ t _ (show 5 < 7 by omega), sv_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [round2, xb, xror, xtern]
  generalize sv t 0 = a at *
  generalize sv t 1 = b at *
  generalize sv t 2 = c at *
  generalize sv t 3 = d at *
  generalize sv t 4 = e at *
  generalize sv t 5 = f at *
  generalize sv t 6 = g at *
  generalize sv t 7 = h at *
  simp only [u0, u1, u2, w0, w1, mB, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' hkw ⊢
  rcases hkw with rfl | rfl <;>
  · simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      reduceVOpExec, isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_128, RegUpd.gpr_setV, RegUpd.mem_setV,
      RegUpd.rd_setV, RegUpd.wr_setV, State.lane, hd, hd', h0, h1, h2, h3, h4, h5, h6, h7, hx,
      Option.some.injEq, exists_eq_left', paddq_eq, ror_eq, tern96_eq, ternCA_eq, ternE8_eq,
      reduceVBinOpSse, BitVec.reduceToNat, Nat.reduceMod]
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7,
      t1_order2, t2_order2, and_self, true_and]
    intro r hr
    rcases hr with rfl | rfl | rfl <;> simp [hd']

/-! ## The round constants -/

theorem flatMap_dup_getD (l : List Word) (t q : Nat) (hq : q < 2) :
    (l.flatMap fun k => [k, k]).getD (2 * t + q) 0 = l.getD t 0 := by
  induction l generalizing t with
  | nil => simp
  | cons a l ih =>
    cases t with
    | zero => rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> simp
    | succ t =>
      rw [show 2 * (t + 1) + q = (2 * t + q) + 2 by omega]
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ]
      exact ih t

/-- Words `2t` and `2t+1` of the table are `Kₜ`. -/
theorem Ks2_getD (t : Nat) {q : Nat} (hq : q < 2) : Ks2.getD (2 * t + q) 0 = K t :=
  flatMap_dup_getD _ t q hq

theorem flatMap_dup_length (l : List Word) : (l.flatMap fun k => [k, k]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem Ks2_length : Ks2.length = 160 := by
  rw [Ks2, flatMap_dup_length, show Spec.Sha512.Ks.length = 80 from rfl]

/-- The index of iteration `j`. -/
abbrev idx2 (j : Nat) : BitVec 64 := BitVec.ofNat 64 (256 * j)

theorem kSlot_ea (s : State) {j : Nat} (h : s.gpr .r9 = idx2 j) (i : Nat) :
    s.ea (kSlot i) = s.gpr .rax + BitVec.ofNat 64 (8 * (4 * (8 * j + i))) := by
  simp only [State.ea, kSlot, h, ofInt_natCast, BitVec.mul_one]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 256 * j + 32 * i = 8 * (4 * (8 * j + i)) by omega]

/-- The table's base register holds its address, and step `i` of iteration
`j` reads `Kₜ` and `Kₜ₊₁` (`t = 16 j + 2 i`), each twice. -/
theorem exec_kSlot2 (s : State) {j : Nat} (i : Nat) (h9 : s.gpr .r9 = idx2 j)
    (hb : s.gpr .rax = s.syms kSym) (hn : 8 * j + i < 40) :
    X86_64.exec (.vmovdquTbl w1 (kSlot i) kSym Ks2) s =
      some (s.setV .l256 w1 (K (16 * j + 2 * i) ++ K (16 * j + 2 * i))
        (K (16 * j + 2 * i + 1) ++ K (16 * j + 2 * i + 1))) := by
  have e : s.ea (kSlot i) - s.syms kSym = BitVec.ofNat 64 (8 * (4 * (8 * j + i))) := by
    rw [kSlot_ea s h9, hb, BitVec.add_comm, BitVec.add_sub_cancel]
  have e' : (BitVec.ofNat 64 (8 * (4 * (8 * j + i)))).toNat = 8 * (4 * (8 * j + i)) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : 4 * (8 * j + i) + 4 ≤ Ks2.length := by rw [Ks2_length]; omega
  have g0 : Ks2.getD (4 * (8 * j + i) + 0) 0 = K (16 * j + 2 * i) := by
    rw [show 4 * (8 * j + i) + 0 = 2 * (16 * j + 2 * i) + 0 by omega, Ks2_getD _ (by omega)]
  have g1 : Ks2.getD (4 * (8 * j + i) + 1) 0 = K (16 * j + 2 * i) := by
    rw [show 4 * (8 * j + i) + 1 = 2 * (16 * j + 2 * i) + 1 by omega, Ks2_getD _ (by omega)]
  have g2 : Ks2.getD (4 * (8 * j + i) + 2) 0 = K (16 * j + 2 * i + 1) := by
    rw [show 4 * (8 * j + i) + 2 = 2 * (16 * j + 2 * i + 1) + 0 by omega, Ks2_getD _ (by omega)]
  have g3 : Ks2.getD (4 * (8 * j + i) + 3) 0 = K (16 * j + 2 * i + 1) := by
    rw [show 4 * (8 * j + i) + 3 = 2 * (16 * j + 2 * i + 1) + 1 by omega, Ks2_getD _ (by omega)]
  simp only [X86_64.exec, e, e', show (kSlot i).base = .rax from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right (4 * (8 * j + i)) (by decide : 0 < 8), hl, and_self, ↓reduceIte, g0, g1, g2, g3]

end VG.Proof.Sha512.X86_64.Avx512
