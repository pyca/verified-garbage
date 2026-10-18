module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Hashing
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the blocks

`acc0` collects in `acc` the checks of `EM`'s last byte, of its leading byte
and of the top bits of `maskedDB` (`acc0_ok`); `posScan` finds the first
nonzero byte of `DB` (`posScan_ok`) and `posCheck` adds its checks to `acc`
(`posCheck_ok`); `copyDb` places `DB` at the start of the cleared buffer
(`copyDb_ok`), which RSAES-OAEP's `shift` then shifts; `cmpH` compares the
digest with `H` and returns whether `acc` is zero (`cmpH_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sK sHD sIdx oEm oBuf oSt oDig oW oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd ea_sp ea_at0 ea_ix0 ofNat_add_lit off_plus off_sub1 nW cpV clrV copy_ok
  clearQ_ok stepR_ok stepI_ok byteLoop_ok)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.RsaPss (lz getD_lt_lz getD_lz_ne)
open VG.Proof.RsaOaep (xor_eq_zero)

/-! ## Bits -/

theorem or_eq_zero64 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · ext i hi; have := congrArg (·[i]) h; simp only [BitVec.getElem_or] at this ⊢; simp_all
    · ext i hi; have := congrArg (·[i]) h; simp only [BitVec.getElem_or] at this ⊢; simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem zext_inj (a b : Byte) : BitVec.setWidth 64 a = BitVec.setWidth 64 b ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])] at this
  · rintro rfl; rfl

theorem zext_eq_zero (a : Byte) : BitVec.setWidth 64 a = 0 ↔ a = 0 := zext_inj a 0

theorem ff_bit (i : Nat) (hi : i < 64) : (255#64)[i] = decide (i < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  by_cases h : i < 8
  · revert h; revert i; decide
  · rw [decide_eq_false h]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (255#64).toNat < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega_using [h])))

theorem zext_and_not (top c : Byte) :
    BitVec.setWidth 64 top &&& (BitVec.setWidth 64 c ^^^ 255#64) = BitVec.setWidth 64 (top &&& ~~~c) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_setWidth, ff_bit i hi]
  by_cases h : i < 8
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge _ _ (by omega_using [h] : 8 ≤ i)]

/-! ## `acc0` -/

/-- `acc` after `acc0`: `EM`'s last byte `⊕ 0xbc`, its first if `lo = 1`, and
the top bits of `maskedDB`'s first. -/
def acc0V (last first top c : Byte) (lo : Nat) : BitVec 64 :=
  (BitVec.setWidth 64 last ^^^ 188#64 ||| BitVec.setWidth 64 first &&& (0#64 - BitVec.ofNat 64 lo)) |||
    BitVec.setWidth 64 top &&& (BitVec.setWidth 64 c ^^^ 255#64)

theorem acc0V_eq_zero (last first top c : Byte) {lo : Nat} (hlo : lo ≤ 1) :
    acc0V last first top c lo = 0 ↔ last = 0xbc ∧ (lo = 1 → first = 0) ∧ top &&& ~~~c = 0 := by
  unfold acc0V
  rw [or_eq_zero64, or_eq_zero64, xor_eq_zero, show (188#64 : BitVec 64) = BitVec.setWidth 64 (0xbc : Byte) from rfl,
    zext_inj, zext_and_not, zext_eq_zero]
  rcases (show lo = 0 ∨ lo = 1 by omega_using [hlo]) with rfl | rfl
  · simp only [show 0#64 - BitVec.ofNat 64 0 = 0 from rfl]
    simp
  · simp only [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, zext_eq_zero]
    simp [and_assoc]


theorem acc0_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k lo : Nat} {c : Byte} (hk : W 23 = BitVec.ofNat 64 k)
    (he : W 33 = off S (oEm + lo)) (hc : W 30 = BitVec.setWidth 64 c) (hlo : W 31 = BitVec.ofNat 64 lo)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) (hlo1 : lo < k) :
    WP isa (.block acc0) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdi, .rax, .r9, .r11, .r10] u u' ∧
      Rep u'.mem F S V (upd W 4 (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) c lo)) := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c1 : oEm = 0 := rfl
  have c5 : oRsa = 8192 := rfl
  have R1 := R.wf L.geo (k := 4) (by decide) (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) c lo)
  refine WP.mono (WP.keep [.rcx, .rdi, .rax, .r9, .r11, .r10] (Q := fun u' => u'.mem = u.mem.writeW (off F sAcc)
    (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) c lo)) ?_ rfl) fun u' ⟨hm, k'⟩ =>
      ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (k'.gpr (by decide)) k'.2.2, k', hm ▸ R1⟩
  · have ea1 : BitVec.ofNat 64 k + (S + BitVec.ofNat 64 oEm) - 1 = off S (oEm + k - 1) := by
      rw [BitVec.add_comm, show S + BitVec.ofNat 64 oEm = off S oEm from rfl, off_plus,
        off_sub1 S (show 1 ≤ oEm + k by omega_arith)]
    xrun [acc0, scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), L.ld (d := sK) (by decide),
      R.rd (d := sK) 23 rfl (by decide), hk, ea1,
      L.sld8 (d := oEm + k - 1) (by omega_arith), R.scr (oEm + k - 1) (by omega_arith),
      L.sld8 (d := oEm) (by omega_arith), R.scr oEm (by omega_arith), L.ld (d := sLo) (by decide),
      R.rd (d := sLo) 31 rfl (by decide), hlo, L.ld (d := sEb) (by decide), R.rd (d := sEb) 33 rfl (by decide), he,
      L.sld8 (d := oEm + lo) (by omega_arith), R.scr (oEm + lo) (by omega_arith), L.ld (d := sC) (by decide),
      R.rd (d := sC) 30 rfl (by decide), hc, L.st (d := sAcc) (by decide)]
    rfl

/-! ## `cmpH` -/

/-- `acc` ORed with the first `j` bytes of the digest `⊕ H`. -/
def orH (V : Nat → Byte) (h acc : BitVec 64) (a b : Nat) : Nat → BitVec 64
  | 0 => acc
  | j + 1 => orH V h acc a b j ||| (BitVec.setWidth 64 (V (a + j)) ^^^ BitVec.setWidth 64 (V (b + j)))

theorem orH_eq_zero (V : Nat → Byte) (h acc : BitVec 64) (a b : Nat) :
    ∀ j, orH V h acc a b j = 0 ↔ acc = 0 ∧ ∀ i < j, V (a + i) = V (b + i)
  | 0 => by simp [orH]
  | j + 1 => by
    rw [orH, or_eq_zero64, orH_eq_zero V h acc a b j, xor_eq_zero, zext_inj]
    constructor
    · rintro ⟨⟨h0, hi⟩, hj⟩
      exact ⟨h0, fun i hi' => if e : i = j then e ▸ hj else hi i (by omega_using [hi', e])⟩
    · rintro ⟨h0, hi⟩
      exact ⟨⟨h0, fun i hi' => hi i (by omega_using [hi'])⟩, hi j (by omega_using [])⟩

/-- `cmp x, 1; sbb rax, rax; and rax, 1`: 1 iff `x = 0`. -/
theorem is_zero (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) &&& 1 =
      if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < (1 : BitVec 64).toNat := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [show (1 : BitVec 64).toNat = 1 from rfl] at h'; show x.toNat = 0; omega_using [h']))
    simp only [this, decide_false, h, ite_false]
    decide

structure CmpI (u₀ : State) (F S : Addr) (V : Nat → Byte) (acc : BitVec 64) (e db : Nat) (j : Nat) (v : State) :
    Prop where
  keep : Keep [.rcx, .rdi, .rdx, .r8, .rax, .r9] u₀ v
  mem : v.mem = u₀.mem
  rcx : v.gpr .rcx = off S oDig
  rdi : v.gpr .rdi = off S (e + db)
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  rdx : v.gpr .rdx = orH V 0 acc oDig (e + db) j

/-- `rax` is 1 if `acc` (word 4) is zero and the digest is `H`, the `D`
bytes after `DB`. -/
theorem cmpH_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db D : Nat} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hD : W 39 = BitVec.ofNat 64 D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hfit : e + db + D ≤ oRsa) :
    WP isa cmpH u fun u' => Keep [.rcx, .rdi, .rdx, .r8, .rax, .r9, .r10] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = if W 4 = 0 ∧ ∀ i < D, V (oDig + i) = V (e + db + i) then 1 else 0 := by
  have c3 : oDig = 3328 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rdx, .r8, .r10] (Q := fun v => v.gpr .rcx = off S oDig ∧
      v.gpr .rdi = off S (e + db) ∧ v.gpr .rdx = W 4 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.gpr .r10 = BitVec.ofNat 64 D ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, h₁₀, hm⟩, hk⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
      L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), L.ld (d := sAcc) (by decide),
      L.ld (d := sHD) (by decide), R.rd (d := sEb) 33 rfl (by decide), R.rd (d := sDb) 44 rfl (by decide),
      R.rd (d := sAcc) 4 rfl (by decide), R.rd (d := sHD) 39 rfl (by decide), he, hdb, hD, off_plus]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.seq (WP.mono (byteLoop_ok (n := D) hD0 (stepR_ok (by omega) v
      (show Reg.r10 ∉ [Reg.rcx, .rdi, .rdx, .r8, .rax, .r9] by decide) (by decide) h₁₀)
      (CmpI v F S V (W 4) e db) ?_ (u := v)
    ⟨Keep.refl _ _, rfl, h₁, h₂, h₄, h₃⟩) fun w J => ?_)
  · intro j hj w J
    have l₁ := Lv.sld8 (d := oDig + j) (by unfold oRsa; omega)
    have l₂ := Lv.sld8 (d := e + db + j) (by omega)
    rw [← J.keep.2.1, ← J.keep.2.2] at l₁ l₂
    refine WP.mono (WP.keep [.rax, .r9, .rdx] (Q := fun w' => w'.mem = w.mem ∧ w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.gpr .rdx = orH V 0 (W 4) oDig (e + db) (j + 1)) ?_ rfl) fun w' ⟨⟨hm', h8, hdx⟩, k'⟩ =>
      ⟨(J.keep.trans k').mono (by decide), h8, fun w'' k'' hm'' h8'' => ⟨(J.keep.trans (k'.trans k'')).mono
        (by decide), by rw [hm'', hm', J.mem], by rw [k''.gpr (by decide), k'.gpr (by decide), J.rcx],
        by rw [k''.gpr (by decide), k'.gpr (by decide), J.rdi], h8'', by rw [k''.gpr (by decide), hdx]⟩⟩
    have r₁ : w.mem (off S (oDig + j)) = V (oDig + j) := by rw [J.mem, hm]; exact R.scr _ (by unfold oRsa; omega)
    have r₂ : w.mem (off S (e + db + j)) = V (e + db + j) := by rw [J.mem, hm]; exact R.scr _ (by omega)
    xrun [ea_ix0, J.rcx, J.rdi, J.r8, J.rdx, off_plus, l₁, l₂, r₁, r₂]
    rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun x => x.mem = w.mem ∧ x.gpr .rax =
      if W 4 = 0 ∧ ∀ i < D, V (oDig + i) = V (e + db + i) then 1 else 0) ?_ rfl)
    fun x ⟨⟨hm', hax⟩, k'⟩ => ⟨(hk.trans (J.keep.trans k')).mono (by decide), by rw [hm', J.mem, hm], hax⟩
  xrun [J.rdx]
  rw [is_zero]
  by_cases hc : W 4 = 0 ∧ ∀ i < D, V (oDig + i) = V (e + db + i)
  · rw [ifp hc, ifp ((orH_eq_zero V 0 _ _ _ _).mpr hc)]
  · rw [ifn hc, ifn (fun h => hc ((orH_eq_zero V 0 _ _ _ _).mp h))]

/-! ## `posScan` -/

/-- The index of the first nonzero value of `f` below `j`. -/
def fnz (f : Nat → Byte) : Nat → Option Nat
  | 0 => none
  | j + 1 => match fnz f j with
    | some i => some i
    | none => if f j = 0 then none else some j

/-- `posScan`'s registers after `j` bytes. -/
structure ScanI (u₀ : State) (S : Addr) (f : Nat → Byte) (e : Nat) (j : Nat) (v : State) : Prop where
  keep : Keep [.rdi, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] u₀ v
  mem : v.mem = u₀.mem
  rdi : v.gpr .rdi = off S e
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  rdx : v.gpr .rdx = if (fnz f j).isSome then BitVec.allOnes 64 else 0
  rsi : v.gpr .rsi = BitVec.ofNat 64 ((fnz f j).getD 0)
  r11 : v.gpr .r11 = BitVec.setWidth 64 (((fnz f j).map f).getD 0)

theorem scan_step (f : Nat → Byte) (j : Nat) :
    let m := (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.setWidth 64 (f j)).toNat <
        BitVec.toNat (1 : BitVec 64)))) ^^^ BitVec.signExtend 64 (4294967295 : BitVec 32)) &&&
      ((if (fnz f j).isSome = true then BitVec.allOnes 64 else 0) ^^^ BitVec.signExtend 64 (4294967295 : BitVec 32))
    ((if (fnz f j).isSome = true then BitVec.allOnes 64 else 0) ||| m =
        if (fnz f (j + 1)).isSome = true then BitVec.allOnes 64 else 0) ∧
      BitVec.ofNat 64 ((fnz f j).getD 0) ||| BitVec.ofNat 64 j &&& m = BitVec.ofNat 64 ((fnz f (j + 1)).getD 0) ∧
      BitVec.setWidth 64 (((fnz f j).map f).getD 0) ||| BitVec.setWidth 64 (f j) &&& m =
        BitVec.setWidth 64 (((fnz f (j + 1)).map f).getD 0) := by
  intro m
  have hs : BitVec.signExtend 64 (4294967295 : BitVec 32) = BitVec.allOnes 64 := by decide
  have hb : 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.setWidth 64 (f j)).toNat <
      BitVec.toNat (1 : BitVec 64)))) = if f j = 0 then BitVec.allOnes 64 else 0 := by
    by_cases h : f j = 0
    · rw [h]; decide
    · have : ¬ (BitVec.setWidth 64 (f j)).toNat < BitVec.toNat (1 : BitVec 64) := fun h' => h (by
        rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at h'
        exact (zext_eq_zero _).mp (BitVec.eq_of_toNat_eq (by show _ = 0; omega_using [h'])))
      simp only [this, decide_false, h, ite_false]
      decide
  cases hF : fnz f j with
  | some i =>
    have hF1 : fnz f (j + 1) = some i := by simp only [fnz, hF]
    simp only [m, hs, hb, hF, hF1]; simp
  | none =>
    by_cases b0 : f j = 0
    · have hF1 : fnz f (j + 1) = none := by simp only [fnz, hF]; exact ifp b0 _ _
      rw [ifp b0] at hb
      simp only [m, hs, hb, hF, hF1]; simp
    · have hF1 : fnz f (j + 1) = some j := by simp only [fnz, hF]; exact ifn b0 _ _
      rw [ifn b0] at hb
      simp only [m, hs, hb, hF, hF1]; simp
      exact ⟨BitVec.and_allOnes, BitVec.and_allOnes⟩

theorem posScan_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hdb1 : 1 ≤ db) (hfit : e + db ≤ oRsa) :
    WP isa posScan u fun u' => Keep [.rdi, .r10, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rdx = (if (fnz (fun i => V (e + i)) db).isSome then BitVec.allOnes 64 else 0) ∧
      u'.gpr .rsi = BitVec.ofNat 64 ((fnz (fun i => V (e + i)) db).getD 0) ∧
      u'.gpr .r11 = BitVec.setWidth 64 (((fnz (fun i => V (e + i)) db).map (fun i => V (e + i))).getD 0) := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .r8, .rdx, .rsi, .r11] (Q := fun v => v.gpr .rdi = off S e ∧
      v.gpr .r10 = BitVec.ofNat 64 db ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.gpr .rdx = 0 ∧ v.gpr .rsi = 0 ∧
      v.gpr .r11 = 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, hm⟩, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), R.rd (d := sEb) 33 rfl (by decide),
      R.rd (d := sDb) 44 rfl (by decide), he, hdb]
  refine WP.mono (byteLoop_ok (n := db) hdb1 (stepR_ok (by unfold oRsa at hfit; omega_using [hfit]) v
      (show Reg.r10 ∉ [Reg.rdi, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] by decide) (by decide) h₂)
    (ScanI v S (fun i => V (e + i)) e) ?_ (u := v) ⟨Keep.refl _ _, rfl, h₁, h₃, by simp [fnz, h₄], by simp [fnz, h₅],
      by simp [fnz, h₆]⟩) fun w J => ⟨(hk.trans J.keep).mono (by decide), J.mem.trans hm, J.rdx, J.rsi, J.r11⟩
  · intro j hj w J
    have l₁ := L.sld8 (d := e + j) (by omega_using [hfit, hj])
    rw [← hk.2.1, ← hk.2.2, ← J.keep.2.1, ← J.keep.2.2] at l₁
    have r₁ : w.mem (off S (e + j)) = V (e + j) := by rw [J.mem, hm]; exact R.scr _ (by omega_using [hfit, hj])
    refine WP.mono (WP.keep [.rax, .r9, .rcx, .rsi, .r11, .rdx] (Q := fun w' => w'.mem = w.mem ∧
        w'.gpr .r8 = BitVec.ofNat 64 j ∧ w'.gpr .rdi = off S e ∧
        w'.gpr .rdx = (if (fnz (fun i => V (e + i)) (j + 1)).isSome then BitVec.allOnes 64 else 0) ∧
        w'.gpr .rsi = BitVec.ofNat 64 ((fnz (fun i => V (e + i)) (j + 1)).getD 0) ∧
        w'.gpr .r11 = BitVec.setWidth 64 (((fnz (fun i => V (e + i)) (j + 1)).map (fun i => V (e + i))).getD 0))
        ?_ rfl) fun w' ⟨⟨hm', h8, hdi, hdx, hsi, h11⟩, k'⟩ => ⟨(J.keep.trans k').mono (by decide), h8,
          fun w'' k'' hm'' h8'' => ⟨(J.keep.trans (k'.trans k'')).mono (by decide), by rw [hm'', hm', J.mem],
            by rw [k''.gpr (by decide), hdi], h8'', by rw [k''.gpr (by decide), hdx], by rw [k''.gpr (by decide), hsi],
            by rw [k''.gpr (by decide), h11]⟩⟩
    xrun [ea_ix0, J.rdi, J.r8, J.rdx, J.rsi, J.r11, off_plus, l₁, r₁]
    exact scan_step (fun i => V (e + i)) j

/-- `fnz` of a list's bytes is `lz`, if that is below `j`. -/
theorem fnz_lz (l : List Byte) : ∀ j ≤ l.length, fnz (fun i => l.getD i 0) j = if lz l < j then some (lz l) else none
  | 0, _ => by simp [fnz]
  | j + 1, hj => by
    have ih := fnz_lz l j (by omega_using [hj])
    simp only [fnz, ih]
    by_cases h : lz l < j
    · rw [ifp h]; exact (ifp (show lz l < j + 1 by omega_using [h]) _ _).symm
    · rw [ifn h]
      by_cases h' : lz l = j
      · subst h'
        rw [ifn (getD_lz_ne (by omega_using [hj])), ifp (by omega_using [])]
      · rw [ifp (getD_lt_lz (by omega_using [h, h'])), ifn (by omega_using [h, h'])]

/-! ## `posCheck` -/

/-- `acc` after `posCheck`: the first nonzero byte is `0x01`, there is one,
and, if the salt's length is fixed, the salt after it has that length. -/
def acc1V (acc : BitVec 64) (fd : Bool) (val : Byte) (fixed : Bool) (sl slen : BitVec 64) : BitVec 64 :=
  (acc ||| ((BitVec.setWidth 64 val ^^^ 1#64) ||| ((if fd then BitVec.allOnes 64 else 0) ^^^ BitVec.allOnes 64))) |||
    (if fixed then sl ^^^ slen else 0)

theorem acc1V_eq_zero (acc : BitVec 64) (fd : Bool) (val : Byte) (fixed : Bool) (sl slen : BitVec 64) :
    acc1V acc fd val fixed sl slen = 0 ↔ acc = 0 ∧ val = 1 ∧ fd = true ∧ (fixed = true → sl = slen) := by
  unfold acc1V
  rw [or_eq_zero64, or_eq_zero64, or_eq_zero64, xor_eq_zero, show (1#64 : BitVec 64) = BitVec.setWidth 64 (1 : Byte)
    from rfl, zext_inj, xor_eq_zero]
  cases fd <;> cases fixed <;> simp [and_assoc]

theorem posCheck_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {db pos : Nat} {fd fixed : Bool} {val : Byte} (hdb : W 44 = BitVec.ofNat 64 db)
    (hany : W 28 = if fixed then 0 else 1) (hpos : pos < db)
    (hdx : u.gpr .rdx = if fd then BitVec.allOnes 64 else 0) (hsi : u.gpr .rsi = BitVec.ofNat 64 pos)
    (h11 : u.gpr .r11 = BitVec.setWidth 64 val) :
    WP isa posCheck u fun u' => Lay u' F S ∧ Keep [.r11, .rdx, .rax, .rcx, .r9] u u' ∧
      Rep u'.mem F S V (upd (upd (upd W 32 (BitVec.ofNat 64 pos)) 4
        (acc1V (W 4) fd val fixed (BitVec.ofNat 64 (db - pos - 1)) (W 29))) 5
        (BitVec.ofNat 64 (db - pos - 1))) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 32) (by decide) (BitVec.ofNat 64 pos)
  rw [show off F (8 * 32) = off F sIdx from rfl] at R1
  have hs : BitVec.signExtend 64 (4294967295 : BitVec 32) = BitVec.allOnes 64 := by decide
  have hsub : BitVec.ofNat 64 db - BitVec.ofNat 64 pos - 1 = BitVec.ofNat 64 (db - pos - 1) := by
    rw [VG.Offset.ofNat_sub_ofNat (show pos ≤ db by omega), show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (show 1 ≤ db - pos by omega)]
  set a1 := W 4 ||| ((BitVec.setWidth 64 val ^^^ 1#64) ||| ((if fd then BitVec.allOnes 64 else 0) ^^^
    BitVec.allOnes 64)) with ha1
  refine WP.seq (WP.mono (WP.keep [.r11, .rdx, .rax, .rcx, .r9] (Q := fun v => v.gpr .rax = a1 ∧
      v.gpr .rcx = BitVec.ofNat 64 (db - pos - 1) ∧ v.zf = some (decide (W 28 = 0)) ∧
      v.mem = u.mem.writeW (off F sIdx) (BitVec.ofNat 64 pos)) ?_ rfl) fun v ⟨⟨h₁, h₂, hz, hm⟩, hk⟩ => ?_)
  · have e44 : (u.mem.writeW (off F sIdx) (BitVec.ofNat 64 pos)).readW (off F sDb) 64 = BitVec.ofNat 64 db := by
      rw [R1.rd (d := sDb) 44 rfl (by decide)]; simp [upd, hdb]
    have e28 : (u.mem.writeW (off F sIdx) (BitVec.ofNat 64 pos)).readW (off F sAny) 64 = W 28 := by
      rw [R1.rd (d := sAny) 28 rfl (by decide)]; simp [upd]
    xrun [ea_sp, L.rsp, L.ld (d := sAcc) (by decide), R.rd (d := sAcc) 4 rfl (by decide), L.st (d := sIdx) (by decide),
      L.ld (d := sDb) (by decide), L.ld (d := sAny) (by decide), e44, e28, hdx, hsi, h11, hs, hsub]
    exact ⟨rfl, by rw [BitVec.and_self]; rfl⟩
  have R1' : Rep v.mem F S V (upd W 32 (BitVec.ofNat 64 pos)) := hm ▸ R1
  have Lv : Lay v F S := L.of_rep' R R1' (by simp [upd]) (hk.gpr (by decide)) hk.2.2
  have hzf : v.zf = some fixed := by rw [hz, hany]; cases fixed <;> decide
  set acc1 := acc1V (W 4) fd val fixed (BitVec.ofNat 64 (db - pos - 1)) (W 29) with hacc1
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.r9, .rax] v w ∧ w.mem = v.mem ∧ w.gpr .rax = acc1)
    ?_ fun w ⟨kw, hmw, haxw⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hzf) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have e29 : v.mem.readW (off F sSlen) 64 = W 29 := by
        rw [R1'.rd (d := sSlen) 29 rfl (by decide)]; simp [upd]
      refine WP.mono (WP.keep [.r9, .rax] (Q := fun w => w.mem = v.mem ∧ w.gpr .rax = acc1) ?_ rfl)
        fun w ⟨h, k'⟩ => ⟨k', h⟩
      xrun [ea_sp, Lv.rsp, Lv.ld (d := sSlen) (by decide), e29, h₁, h₂]
      simp only [hacc1, acc1V, ha1, ite_true]
    · subst hb
      refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
      · xrun
      · subst hw
        refine ⟨Keep.refl _ _, rfl, ?_⟩
        rw [h₁, hacc1, acc1V, ha1]; simp
  have Lw : Lay w F S := Lv.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  have Rw : Rep w.mem F S V (upd W 32 (BitVec.ofNat 64 pos)) := hmw ▸ R1'
  have R2 := (Rw.wf G' (k := 4) (by decide) acc1).wf G' (k := 5) (by decide) (BitVec.ofNat 64 (db - pos - 1))
  rw [show off F (8 * 4) = off F sAcc from rfl, show off F (8 * 5) = off F sL from rfl] at R2
  refine WP.mono (WP.keep [.rcx] (Q := fun x => x.mem = (w.mem.writeW (off F sAcc) acc1).writeW (off F sL)
      (BitVec.ofNat 64 (db - pos - 1))) ?_ rfl) fun x ⟨hmx, kx⟩ =>
    ⟨Lw.of_rep' Rw (hmx ▸ R2) (by simp [upd]) (kx.gpr (by decide)) kx.2.2,
      (hk.trans (kw.trans kx)).mono (by decide), hmx ▸ R2⟩
  xrun [ea_sp, Lw.rsp, Lw.st (d := sAcc) (by decide), Lw.st (d := sL) (by decide), haxw,
    (kw.gpr (by decide)).trans h₂]

end VG.Proof.RsaPss.X86_64
