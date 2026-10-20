module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sym
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Sym
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-!
# ML-KEM on x86-64: the NTT on registers, word by word, agrees

The terms of `Sym.run` hold in the machine (`Rel`): each word of a register
or of a region that is not `junk` is the value of its term (`E.eval`), given
the polynomial's words after each number of layers (`L`) and their reduced
values (`O`), which obey the butterflies and the reduction (`Model`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

/-! ## Values of terms -/

/-- `vmont` of the word `b` with the zetas `z` and `z'`. -/
def mtW (b : BitVec 16) (z z' : Nat) : BitVec 16 :=
  (mulWordsSigned b (BitVec.ofNat 16 z)).extractLsb' 16 16 -
    (mulWordsSigned ((mulWordsSigned b (BitVec.ofNat 16 z')).extractLsb' 0 16) (BitVec.ofNat 16 qN)).extractLsb' 16 16

/-- `vcadd` of the word `r`. -/
def caddQ (r : BitVec 16) : BitVec 16 := r + (r.sshiftRight (min 15 16) &&& BitVec.ofNat 16 qN)

def E.eval (L : Nat → Nat → BitVec 16) (O : Nat → BitVec 16) : E → BitVec 16
  | .lv st p => L st p
  | .out p => O p
  | .c v => BitVec.ofNat 16 v
  | .add a b => a.eval L O + b.eval L O
  | .sub a b => a.eval L O - b.eval L O
  | .mlo a b => (mulWordsSigned (a.eval L O) (b.eval L O)).extractLsb' 0 16
  | .mhi a b => (mulWordsSigned (a.eval L O) (b.eval L O)).extractLsb' 16 16
  | .sra a => (a.eval L O).sshiftRight (min 15 16)
  | .and a b => a.eval L O &&& b.eval L O
  | .junk => 0

/-- The words after each number of layers obey the layers of `R`, the
input's are below `2¹⁵`, and `O` is the reduction of the last ones. -/
structure Model (R : Rules) (L : Nat → Nat → BitVec 16) (O : Nat → BitVec 16) : Prop where
  small : ∀ p < 256, (L 0 p).toNat < 32768
  bfly : ∀ st p p' z z', bflyOk R st p p' z z' = true →
    L (st + 1) p = L st p + mtW (L st p') z z' ∧ L (st + 1) p' = L st p - mtW (L st p') z z'
  gsSum : ∀ st p p', gsPairOk R st p p' = true → L (st + 1) p = L st p + L st p'
  gsDiff : ∀ st p p' z z', gsOk R st p p' z z' = true → L (st + 1) p' = mtW (L st p' - L st p) z z'
  red : ∀ st p, redOk R st = true → p < 256 → L (st + 1) p = mtW (L st p) (zmTab 0) (zmTab 0 * qinvN % 65536)
  out : ∀ p < 256, O p = caddQ (mtW (L R.ops.length p) R.fin (R.fin * qinvN % 65536))

/-- The term `e` holds of the word `w`. -/
def Hd (L : Nat → Nat → BitVec 16) (O : Nat → BitVec 16) (e : E) (w : BitVec 16) : Prop :=
  e.isJunk = true ∨ w = e.eval L O

section
variable {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem Hd.junk (w : BitVec 16) : Hd L O .junk w := .inl rfl

theorem E.beq_eq : ∀ {a b : E}, E.beq a b = true → a = b := by
  intro a
  induction a with
  | lv => intro b h; cases b <;> simp_all [E.beq]
  | out => intro b h; cases b <;> simp_all [E.beq]
  | c => intro b h; cases b <;> simp_all [E.beq]
  | add a b iha ihb => intro x h; cases x <;> simp only [E.beq, Bool.and_eq_true, reduceCtorEq] at h ⊢ <;>
      rw [iha h.1, ihb h.2]
  | sub a b iha ihb => intro x h; cases x <;> simp only [E.beq, Bool.and_eq_true, reduceCtorEq] at h ⊢ <;>
      rw [iha h.1, ihb h.2]
  | mlo a b iha ihb => intro x h; cases x <;> simp only [E.beq, Bool.and_eq_true, reduceCtorEq] at h ⊢ <;>
      rw [iha h.1, ihb h.2]
  | mhi a b iha ihb => intro x h; cases x <;> simp only [E.beq, Bool.and_eq_true, reduceCtorEq] at h ⊢ <;>
      rw [iha h.1, ihb h.2]
  | and a b iha ihb => intro x h; cases x <;> simp only [E.beq, Bool.and_eq_true, reduceCtorEq] at h ⊢ <;>
      rw [iha h.1, ihb h.2]
  | sra a iha => intro x h; cases x <;> simp only [E.beq, reduceCtorEq] at h ⊢; rw [iha h]
  | junk => intro b h; cases b <;> simp_all [E.beq]

theorem Hd.of_eq {e : E} {w : BitVec 16} (h : w = e.eval L O) : Hd L O e w := .inr h

theorem Hd.eq {e : E} {w : BitVec 16} (h : Hd L O e w) (hj : e.isJunk = false) : w = e.eval L O :=
  h.resolve_left (by rw [hj]; decide)

theorem isJunk_or (a b : E) (h : (a.isJunk || b.isJunk) = false) : a.isJunk = false ∧ b.isJunk = false := by
  simp only [Bool.or_eq_false_iff] at h; exact h

theorem mk2_ok (f : E → E → E) (g : BitVec 16 → BitVec 16 → BitVec 16)
    (hf : ∀ a b, (f a b).eval L O = g (a.eval L O) (b.eval L O)) {a b : E} {x y : BitVec 16}
    (ha : Hd L O a x) (hb : Hd L O b y) : Hd L O (mk2 f a b) (g x y) := by
  unfold mk2
  split
  · exact Hd.junk _
  · rename_i h
    obtain ⟨h1, h2⟩ := isJunk_or a b (by simpa using h)
    exact Hd.of_eq (by rw [hf, ← ha.eq h1, ← hb.eq h2])

theorem mkSra_ok {a : E} {x : BitVec 16} (ha : Hd L O a x) :
    Hd L O (mkSra a) (x.sshiftRight (min 15 16)) := by
  unfold mkSra
  split
  · exact Hd.junk _
  · rename_i h
    exact Hd.of_eq (by simp only [E.eval]; rw [← ha.eq (by simpa using h)])

theorem eval_mt (b : E) (z z' : Nat) : (mt b z z').eval L O = mtW (b.eval L O) z z' := rfl

theorem mkAdd_ok {R : Rules} (hM : Model R L O) {a b : E} {x y : BitVec 16} (ha : Hd L O a x) (hb : Hd L O b y) :
    Hd L O (mkAdd R a b) (x + y) := by
  unfold mkAdd
  split
  · exact Hd.junk _
  rename_i hj
  obtain ⟨h1, h2⟩ := isJunk_or a b (by simpa using hj)
  rw [ha.eq h1, hb.eq h2]
  split
  · split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hb'⟩ := hc
      exact Hd.of_eq (by simp only [E.eval]; exact ((hM.bfly _ _ _ _ _ hb').1).symm ▸ rfl)
    · exact Hd.of_eq rfl
  · split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hp⟩ := hc
      exact Hd.of_eq (by simp only [E.eval]; exact (hM.gsSum _ _ _ hp).symm ▸ rfl)
    · exact Hd.of_eq rfl
  · split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hr⟩, hp⟩ := hc
      obtain rfl := E.beq_eq hr
      refine Hd.of_eq ?_
      simp only [E.eval]
      rw [hM.out _ hp]
      rfl
    · exact Hd.of_eq rfl
  · exact Hd.of_eq rfl

theorem mkSub_ok {R : Rules} (hM : Model R L O) {a b : E} {x y : BitVec 16} (ha : Hd L O a x) (hb : Hd L O b y) :
    Hd L O (mkSub R a b) (x - y) := by
  unfold mkSub
  split
  · exact Hd.junk _
  rename_i hj
  obtain ⟨h1, h2⟩ := isJunk_or a b (by simpa using hj)
  rw [ha.eq h1, hb.eq h2]
  split
  · split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hb'⟩ := hc
      exact Hd.of_eq (by simp only [E.eval]; exact ((hM.bfly _ _ _ _ _ hb').2).symm ▸ rfl)
    · exact Hd.of_eq rfl
  · split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hg⟩ := hc
      exact Hd.of_eq (by simp only [E.eval]; exact (hM.gsDiff _ _ _ _ _ hg).symm ▸ rfl)
    · exact Hd.of_eq rfl
  · split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hr⟩, hp⟩ := hc
      exact Hd.of_eq (by simp only [E.eval]; exact (hM.red _ _ hr hp).symm ▸ rfl)
    · exact Hd.of_eq rfl
  · exact Hd.of_eq rfl

theorem pk_ok {R : Rules} (hM : Model R L O) {lo hi : E} {x : BitVec 128} {j : Nat} (hj : j < 4)
    (hl : Hd L O lo (word x (2 * j))) (hh : Hd L O hi (word x (2 * j + 1))) :
    Hd L O (pk lo hi) (satSignedWord (dword x j)) := by
  unfold pk
  split
  · rename_i p
    split
    · rename_i hp
      refine Hd.of_eq ?_
      have e1 : word x (2 * j) = L 0 p := hl.eq rfl
      have e2 : word x (2 * j + 1) = 0 := hh.eq rfl
      have hd : (dword x j).toNat = (L 0 p).toNat := by rw [dword_eq_words x hj, e1, e2]; simp
      have hs := hM.small p hp
      apply BitVec.eq_of_toNat_eq
      rw [satSignedWord_small (by rw [hd]; exact hs), BitVec.toNat_setWidth, hd]
      simp only [E.eval]
      exact Nat.mod_eq_of_lt (by omega)
    · exact Hd.junk _
  · exact Hd.junk _

end

/-! ## Words of registers -/

/-- Word `e` (`e < 16`) of `ymm r`. -/
def wd (s : State) (r : XReg) (e : Nat) : BitVec 16 := word (s.lane r (e / 8)) (e % 8)

theorem xr_xi (r : XReg) : xr (xi r) = r := by cases r <;> rfl

theorem xi_inj {r r' : XReg} : xi r = xi r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

theorem xi_lt (r : XReg) : xi r < 16 := by cases r <;> decide

theorem wd_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) {e : Nat} :
    wd (s.setV .l256 d lo hi) r e = if r = d then word (if e / 8 = 0 then lo else hi) (e % 8) else wd s r e := by
  simp only [wd, State.lane_setV256]
  split <;> rfl

theorem lane_sel (s : State) (r : XReg) {e : Nat} (he : e < 16) :
    (if e / 8 = 0 then s.lane r 0 else s.lane r 1) = s.lane r (e / 8) := by
  by_cases h : e / 8 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), h]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), show e / 8 = 1 by omega]

/-- Word `e` of a 256-bit value, as `setV` splits it. -/
theorem word_split (x : BitVec 256) {e : Nat} (he : e < 16) :
    word (if e / 8 = 0 then x.extractLsb' 0 128 else x.extractLsb' 128 128) (e % 8) = x.extractLsb' (16 * e) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  by_cases h : e / 8 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [word, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (e % 8) + j < 128 by omega)]
    exact congrArg _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    simp only [word, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (e % 8) + j < 128 by omega)]
    exact congrArg _ (by omega)

theorem ymm_word (s : State) (r : XReg) {e : Nat} (he : e < 16) : (s.ymm r).extractLsb' (16 * e) 16 = wd s r e := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [wd, State.ymm, State.lane, word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj,
    decide_true, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 16 * e + j < 128 by omega, ite_true, show e / 8 = 0 by omega]
    exact congrArg _ (by omega)
  · simp only [show ¬ 16 * e + j < 128 by omega, ite_false, show e / 8 = 1 by omega, Nat.one_ne_zero]
    exact congrArg _ (by omega)

/-! ## Words of the instructions -/

theorem word_eq_qword (x : BitVec 128) {i : Nat} (_hi : i < 8) :
    word x i = (qword x (i / 4)).extractLsb' (16 * (i % 4)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [word, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 16 * (i % 4) + j < 64 by omega)]
  exact congrArg _ (by omega)

theorem qword_shift (x : BitVec 128) (op : XShiftOp) (hop : op = .psllq ∨ op = .psrlq) {k : Nat} (hk : k < 2) :
    qword (XShiftOp.eval op x 32) k = if op = .psllq then qword x k <<< 32 else qword x k >>> 32 := by
  rcases hop with rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
    simp [XShiftOp.eval, Proof.Poly1305.X86_64.Avx2.qword_app0, Proof.Poly1305.X86_64.Avx2.qword_app1]

theorem word_psllq32 (x : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XShiftOp.eval .psllq x 32) i = if i % 4 < 2 then 0 else word x (i - 2) := by
  rw [word_eq_qword _ hi, qword_shift _ _ (.inl rfl) (by omega), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  split
  · simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and]
    simp only [decide_eq_true (show 16 * (i % 4) + j < 64 by omega), decide_eq_true (show 16 * (i % 4) + j < 32 by omega)]
    simp
  · rw [word_eq_qword _ (by omega)]
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and,
      decide_eq_true (show 16 * (i % 4) + j < 64 by omega), decide_eq_false (show ¬ 16 * (i % 4) + j < 32 by omega),
      Bool.not_false, Bool.true_and, show (i - 2) / 4 = i / 4 by omega]
    exact congrArg _ (by omega)

theorem word_psrlq32 (x : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XShiftOp.eval .psrlq x 32) i = if i % 4 < 2 then word x (i + 2) else 0 := by
  rw [word_eq_qword _ hi, qword_shift _ _ (.inr rfl) (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  split
  · rw [word_eq_qword _ (by omega)]
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and,
      show (i + 2) / 4 = i / 4 by omega]
    exact congrArg _ (by omega)
  · simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp

theorem word_blend (x y : BitVec 128) (imm : BitVec 4) {i : Nat} (hi : i < 8) :
    word (blendDwords x y imm) i = if imm.getLsbD (i / 2) then word y i else word x i := by
  rw [blendDwords, word_eq_dword _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceDiv, Nat.reduceMod, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3] <;> split <;> rw [word_eq_dword _ (by decide)] <;> rfl

/-! ## The machine's relation -/

/-- The base of region `k`. -/
def rbase (rs : List Rg) (s₀ : State) (k : Nat) : Addr :=
  s₀.gpr (rs.getD k default).1 + BitVec.ofNat 64 (rs.getD k default).2.1

/-- The number of words of region `k`. -/
def rlen (rs : List Rg) (k : Nat) : Nat := (rs.getD k default).2.2.1

/-- The regions are readable (writable if the code writes them), apart,
short, and `r8` holds the table's address. -/
structure Ctx (rs : List Rg) (s₀ : State) : Prop where
  rd : ∀ k < rs.length, InRegions (s₀.rd ++ s₀.wr) (rbase rs s₀ k) (2 * rlen rs k)
  wr : ∀ k < rs.length, (rs.getD k default).2.2.2 = true → InRegions s₀.wr (rbase rs s₀ k) (2 * rlen rs k)
  sep : ∀ k k', k < rs.length → k' < rs.length → k ≠ k' →
    Mem.Sep (rbase rs s₀ k) (2 * rlen rs k) (rbase rs s₀ k') (2 * rlen rs k')
  short : ∀ k < rs.length, 2 * rlen rs k < 2 ^ 32 ∧ (rs.getD k default).2.1 < 2 ^ 32
  r8 : s₀.gpr .r8 = s₀.syms tblName

/-- `s₀` with the vector registers and the memory of `s`. -/
def vm (s₀ s : State) : State := { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, mem := s.mem }

structure Rel (rs : List Rg) (L : Nat → Nat → BitVec 16) (O : Nat → BitVec 16) (σ : St) (s₀ s : State) : Prop where
  reg : ∀ r e, e < 16 → Hd L O ((σ.reg r).get e) (wd s r e)
  mem : ∀ k j, k < rs.length → j < rlen rs k →
    Hd L O (Y.get ((σ.mem.getD k []).getD (j / 16) []) (j % 16)) (wordAt s.mem (rbase rs s₀ k) j)
  eq : vm s₀ s = s
  len : σ.mem.length = rs.length ∧ σ.regs.length = 16
  /-- Memory changes only in the regions the code writes. -/
  fr : ∀ x, (∀ k < rs.length, (rs.getD k default).2.2.2 = true → ¬ (x - rbase rs s₀ k).toNat < 2 * rlen rs k) →
    s.mem x = s₀.mem x

theorem Rel.gpr {rs L O σ s₀ s} (h : Rel rs L O σ s₀ s) : s.gpr = s₀.gpr := by rw [← h.eq]; rfl
theorem Rel.wr {rs L O σ s₀ s} (h : Rel rs L O σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem Rel.rd {rs L O σ s₀ s} (h : Rel rs L O σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem Rel.syms {rs L O σ s₀ s} (h : Rel rs L O σ s₀ s) : s.syms = s₀.syms := by rw [← h.eq]; rfl

theorem St.reg_set (σ : St) (d r : XReg) (v : Y) (hl : σ.regs.length = 16) :
    (σ.set d v).reg r = if r = d then v else σ.reg r := by
  simp only [St.reg, St.set]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  split
  · rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true (xi_inj.1 h.symm)), ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl]; exact xi_lt d))]; rfl
  · rename_i h
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => h (congrArg xi e).symm)), List.getD_eq_getElem?_getD]

/-- A register written with words whose terms hold. -/
theorem Rel.setReg {rs L O σ s₀ s} (h : Rel rs L O σ s₀ s) {d : XReg} {v : Y} {s' : State}
    (hd : ∀ e, e < 16 → Hd L O (v.get e) (wd s' d e)) (ho : ∀ r, r ≠ d → ∀ e, e < 16 → wd s' r e = wd s r e)
    (hm : s'.mem = s.mem) (he : vm s₀ s' = s') : Rel rs L O (σ.set d v) s₀ s' := by
  refine ⟨fun r e hr => ?_, fun k j hk hj => ?_, he, ?_, ?_⟩
  · rw [St.reg_set _ _ _ _ h.len.2]
    split
    · rename_i hr'; subst hr'; exact hd e hr
    · rename_i hr'; rw [ho r hr' e hr]; exact h.reg r e hr
  · rw [hm]; exact h.mem k j hk hj
  · exact ⟨h.len.1, by simp only [St.set, List.length_set, h.len.2]⟩
  · intro x hx; rw [hm]; exact h.fr x hx

theorem vm_setV {s₀ s : State} (h : vm s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    vm s₀ (s.setV len d lo hi) = s.setV len d lo hi := by rw [← h]; rfl

theorem vm_vop {s₀ s : State} (h : vm s₀ s = s) (o : VOp) (ho : o ≠ .vzeroupper) : vm s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> first | rfl | exact absurd rfl ho

end VG.Proof.MlKem.X86_64.NttR
