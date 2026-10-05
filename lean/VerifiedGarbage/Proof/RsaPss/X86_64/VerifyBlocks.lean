import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.RsaPss.VerifyCases

/-!
# RSASSA-PSS verification on x86-64: the blocks

`acc0` collects in `acc` the checks of `EM`'s last byte, of its leading byte
and of the top bits of `maskedDB` (`acc0_ok`); `posScan` finds the first
nonzero byte of `DB` (`posScan_ok`) and `posCheck` adds its checks to `acc`
(`posCheck_ok`); `copyDb` and `shift` place the salt after `mHash` in `Y`
(`copyDb_ok`, `shift_ok`); `cmpH` compares the digest with `H` and returns
whether `acc` is zero (`cmpH_ok`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off Scr off_off ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

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
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · rintro rfl; rfl

theorem zext_eq_zero (a : Byte) : BitVec.setWidth 64 a = 0 ↔ a = 0 := zext_inj a 0

theorem ff_bit (i : Nat) (hi : i < 64) : (255#64)[i] = decide (i < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  by_cases h : i < 8
  · revert h; revert i; decide
  · rw [decide_eq_false h]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (255#64).toNat < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega)))

theorem zext_and_not (top c : Byte) :
    BitVec.setWidth 64 top &&& (BitVec.setWidth 64 c ^^^ 255#64) = BitVec.setWidth 64 (top &&& ~~~c) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_setWidth, ff_bit i hi]
  by_cases h : i < 8
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge _ _ (by omega : 8 ≤ i)]

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
  rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
  · simp only [show 0#64 - BitVec.ofNat 64 0 = 0 from rfl]
    simp
  · simp only [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, zext_eq_zero]
    simp [and_assoc]


theorem acc0_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k lo : Nat} {c : Byte} (hk : W 17 = BitVec.ofNat 64 k)
    (he : W 23 = off S (oEm + lo)) (hc : W 25 = BitVec.setWidth 64 c) (hlo : W 26 = BitVec.ofNat 64 lo)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) (hlo1 : lo < k) :
    WP isa (.block acc0) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdi, .rax, .r9, .r11] u u' ∧
      Rep u'.mem F S V (upd W 33 (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) c lo)) := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  have R1 := R.wf L.geo (k := 33) (by decide) (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) c lo)
  refine WP.mono (WP.keep [.rcx, .rdi, .rax, .r9, .r11] (Q := fun u' => u'.mem = u.mem.writeW (off F sAcc)
    (acc0V (V (oEm + k - 1)) (V oEm) (V (oEm + lo)) c lo)) ?_ rfl) fun u' ⟨hm, k'⟩ =>
      ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (k'.gpr (by decide)) k'.2.2, k', hm ▸ R1⟩
  · xrun [acc0, scr, List.cons_append, List.nil_append, ea_sp, ea_at0, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), L.ld (d := sK) (by decide),
      R.rd (d := sK) 17 rfl (by decide), hk, off_plus, off_sub1 S (show 1 ≤ oEm + k by omega),
      L.sld8 (d := oEm + k - 1) (by omega), R.scr (oEm + k - 1) (by omega),
      L.sld8 (d := oEm) (by omega), R.scr oEm (by omega), L.ld (d := sLo) (by decide),
      R.rd (d := sLo) 26 rfl (by decide), hlo, L.ld (d := sEb) (by decide), R.rd (d := sEb) 23 rfl (by decide), he,
      L.sld8 (d := oEm + lo) (by omega), R.scr (oEm + lo) (by omega), L.ld (d := sC) (by decide),
      R.rd (d := sC) 25 rfl (by decide), hc, L.st (d := sAcc) (by decide)]
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
      exact ⟨h0, fun i hi' => if e : i = j then e ▸ hj else hi i (by omega)⟩
    · rintro ⟨h0, hi⟩
      exact ⟨⟨h0, fun i hi' => hi i (by omega)⟩, hi j (by omega)⟩

/-- `cmp x, 1; sbb rax, rax; and rax, 1`: 1 iff `x = 0`. -/
theorem is_zero (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) &&& 1 =
      if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < (1 : BitVec 64).toNat := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [show (1 : BitVec 64).toNat = 1 from rfl] at h'; show x.toNat = 0; omega))
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

variable {H : Hash} (hH : Proof.Pbkdf2.Md.X86_64.HashOK H)

include hH in
/-- `rax` is 1 if `acc` is zero and the digest is `H`, the `hLen` bytes after
`DB`. -/
theorem cmpH_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hfit : e + db + H.D ≤ oRsa) :
    WP isa (cmpH H) u fun u' => Keep [.rcx, .rdi, .rdx, .r8, .rax, .r9] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = if W 33 = 0 ∧ ∀ i < H.D, V (oDig + i) = V (e + db + i) then 1 else 0 := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c3 : oDig = 2304 := rfl
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rdx, .r8] (Q := fun v => v.gpr .rcx = off S oDig ∧
      v.gpr .rdi = off S (e + db) ∧ v.gpr .rdx = W 33 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, hm⟩, hk⟩ => ?_)
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide), L.ld (d := sEb) (by decide),
      L.ld (d := sDb) (by decide), L.ld (d := sAcc) (by decide), R.rd (d := sEb) 23 rfl (by decide),
      R.rd (d := sDb) 24 rfl (by decide), R.rd (d := sAcc) 33 rfl (by decide), he, hdb, off_plus]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.seq (WP.mono (byteLoop_ok (n := H.D) hD (stepI_ok (show H.D < 2 ^ 31 by omega) u
      [.rcx, .rdi, .rdx, .r8, .rax, .r9]) (CmpI u F S V (W 33) e db) ?_ (u := v)
    ⟨hk.mono (by decide), hm, h₁, h₂, h₄, h₃⟩) fun w J => ?_)
  · intro j hj w J
    have l₁ := Lv.sld8 (d := oDig + j) (by unfold oRsa; omega)
    have l₂ := Lv.sld8 (d := e + db + j) (by omega)
    rw [hk.2.1, hk.2.2, ← J.keep.2.1, ← J.keep.2.2] at l₁ l₂
    refine WP.mono (WP.keep [.rax, .r9, .rdx] (Q := fun w' => w'.mem = w.mem ∧ w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.gpr .rdx = orH V 0 (W 33) oDig (e + db) (j + 1)) ?_ rfl) fun w' ⟨⟨hm', h8, hdx⟩, k'⟩ =>
      ⟨(J.keep.trans k').mono (by decide), h8, fun w'' k'' hm'' h8'' => ⟨(J.keep.trans (k'.trans k'')).mono
        (by decide), by rw [hm'', hm', J.mem], by rw [k''.gpr (by decide), k'.gpr (by decide), J.rcx],
        by rw [k''.gpr (by decide), k'.gpr (by decide), J.rdi], h8'', by rw [k''.gpr (by decide), hdx]⟩⟩
    have r₁ : w.mem (off S (oDig + j)) = V (oDig + j) := by rw [J.mem]; exact R.scr _ (by unfold oRsa; omega)
    have r₂ : w.mem (off S (e + db + j)) = V (e + db + j) := by rw [J.mem]; exact R.scr _ (by omega)
    xrun [ea_ix0, J.rcx, J.rdi, J.r8, J.rdx, off_plus, l₁, l₂, r₁, r₂]
    rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun x => x.mem = w.mem ∧ x.gpr .rax =
      if W 33 = 0 ∧ ∀ i < H.D, V (oDig + i) = V (e + db + i) then 1 else 0) ?_ rfl)
    fun x ⟨⟨hm', hax⟩, k'⟩ => ⟨(J.keep.trans k').mono (by decide), by rw [hm', J.mem], hax⟩
  xrun [J.rdx]
  rw [is_zero]
  by_cases hc : W 33 = 0 ∧ ∀ i < H.D, V (oDig + i) = V (e + db + i)
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
        exact (zext_eq_zero _).mp (BitVec.eq_of_toNat_eq (by show _ = 0; omega)))
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
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hdb1 : 1 ≤ db) (hfit : e + db ≤ oRsa) :
    WP isa posScan u fun u' => Keep [.rdi, .r10, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rdx = (if (fnz (fun i => V (e + i)) db).isSome then BitVec.allOnes 64 else 0) ∧
      u'.gpr .rsi = BitVec.ofNat 64 ((fnz (fun i => V (e + i)) db).getD 0) ∧
      u'.gpr .r11 = BitVec.setWidth 64 (((fnz (fun i => V (e + i)) db).map (fun i => V (e + i))).getD 0) := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .r8, .rdx, .rsi, .r11] (Q := fun v => v.gpr .rdi = off S e ∧
      v.gpr .r10 = BitVec.ofNat 64 db ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.gpr .rdx = 0 ∧ v.gpr .rsi = 0 ∧
      v.gpr .r11 = 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, hm⟩, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), R.rd (d := sEb) 23 rfl (by decide),
      R.rd (d := sDb) 24 rfl (by decide), he, hdb]
  refine WP.mono (byteLoop_ok (n := db) hdb1 (stepR_ok (by unfold oRsa at hfit; omega) v
      (show Reg.r10 ∉ [Reg.rdi, .r8, .rdx, .rsi, .r11, .rax, .r9, .rcx] by decide) (by decide) h₂)
    (ScanI v S (fun i => V (e + i)) e) ?_ (u := v) ⟨Keep.refl _ _, rfl, h₁, h₃, by simp [fnz, h₄], by simp [fnz, h₅],
      by simp [fnz, h₆]⟩) fun w J => ⟨(hk.trans J.keep).mono (by decide), J.mem.trans hm, J.rdx, J.rsi, J.r11⟩
  · intro j hj w J
    have l₁ := L.sld8 (d := e + j) (by omega)
    rw [← hk.2.1, ← hk.2.2, ← J.keep.2.1, ← J.keep.2.2] at l₁
    have r₁ : w.mem (off S (e + j)) = V (e + j) := by rw [J.mem, hm]; exact R.scr _ (by omega)
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
    have ih := fnz_lz l j (by omega)
    simp only [fnz, ih]
    by_cases h : lz l < j
    · rw [ifp h]; exact (ifp (show lz l < j + 1 by omega) _ _).symm
    · rw [ifn h]
      by_cases h' : lz l = j
      · subst h'
        rw [ifn (getD_lz_ne (by omega)), ifp (by omega)]
      · rw [ifp (getD_lt_lz (by omega)), ifn (by omega)]

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

include hH in
theorem posCheck_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {db pos : Nat} {fd fixed : Bool} {val : Byte} (hdb : W 24 = BitVec.ofNat 64 db)
    (hany : W 35 = if fixed then 0 else 1) (hpos : pos < db)
    (hdx : u.gpr .rdx = if fd then BitVec.allOnes 64 else 0) (hsi : u.gpr .rsi = BitVec.ofNat 64 pos)
    (h11 : u.gpr .r11 = BitVec.setWidth 64 val) :
    WP isa (posCheck H) u fun u' => Lay u' F S ∧ Keep [.r11, .rdx, .rax, .rcx, .r9] u u' ∧
      Rep u'.mem F S V (upd (upd (upd W 34 (BitVec.ofNat 64 pos)) 33
        (acc1V (W 33) fd val fixed (BitVec.ofNat 64 (db - pos - 1)) (W 36))) 27
        (BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)))) := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have G' := L.geo
  have R1 := R.wf G' (k := 34) (by decide) (BitVec.ofNat 64 pos)
  rw [show off F (8 * 34) = off F sPos from rfl] at R1
  have hs : BitVec.signExtend 64 (4294967295 : BitVec 32) = BitVec.allOnes 64 := by decide
  have hsub : BitVec.ofNat 64 db - BitVec.ofNat 64 pos - 1 = BitVec.ofNat 64 (db - pos - 1) := by
    rw [VG.Offset.ofNat_sub_ofNat (show pos ≤ db by omega), show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (show 1 ≤ db - pos by omega)]
  set a1 := W 33 ||| ((BitVec.setWidth 64 val ^^^ 1#64) ||| ((if fd then BitVec.allOnes 64 else 0) ^^^
    BitVec.allOnes 64)) with ha1
  refine WP.seq (WP.mono (WP.keep [.r11, .rdx, .rax, .rcx, .r9] (Q := fun v => v.gpr .rax = a1 ∧
      v.gpr .rcx = BitVec.ofNat 64 (db - pos - 1) ∧ v.zf = some (decide (W 35 = 0)) ∧
      v.mem = u.mem.writeW (off F sPos) (BitVec.ofNat 64 pos)) ?_ rfl) fun v ⟨⟨h₁, h₂, hz, hm⟩, hk⟩ => ?_)
  · have e24 : (u.mem.writeW (off F sPos) (BitVec.ofNat 64 pos)).readW (off F sDb) 64 = BitVec.ofNat 64 db := by
      rw [R1.rd (d := sDb) 24 rfl (by decide)]; simp [upd, hdb]
    have e35 : (u.mem.writeW (off F sPos) (BitVec.ofNat 64 pos)).readW (off F sAny) 64 = W 35 := by
      rw [R1.rd (d := sAny) 35 rfl (by decide)]; simp [upd]
    xrun [ea_sp, L.rsp, L.ld (d := sAcc) (by decide), R.rd (d := sAcc) 33 rfl (by decide), L.st (d := sPos) (by decide),
      L.ld (d := sDb) (by decide), L.ld (d := sAny) (by decide), e24, e35, hdx, hsi, h11, hs, hsub]
    exact ⟨rfl, by rw [BitVec.and_self]; rfl⟩
  have R1' : Rep v.mem F S V (upd W 34 (BitVec.ofNat 64 pos)) := hm ▸ R1
  have Lv : Lay v F S := L.of_rep' R R1' (by simp [upd]) (hk.gpr (by decide)) hk.2.2
  have hzf : v.zf = some fixed := by rw [hz, hany]; cases fixed <;> decide
  set acc1 := acc1V (W 33) fd val fixed (BitVec.ofNat 64 (db - pos - 1)) (W 36) with hacc1
  refine WP.seq (WP.mono (Q := fun (w : State) => Keep [.r9, .rax] v w ∧ w.mem = v.mem ∧ w.gpr .rax = acc1)
    ?_ fun w ⟨kw, hmw, haxw⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .e v = _ from hzf) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have e36 : v.mem.readW (off F sSlen) 64 = W 36 := by
        rw [R1'.rd (d := sSlen) 36 rfl (by decide)]; simp [upd]
      refine WP.mono (WP.keep [.r9, .rax] (Q := fun w => w.mem = v.mem ∧ w.gpr .rax = acc1) ?_ rfl)
        fun w ⟨h, k'⟩ => ⟨k', h⟩
      xrun [ea_sp, Lv.rsp, Lv.ld (d := sSlen) (by decide), e36, h₁, h₂]
      simp only [hacc1, acc1V, ha1, ite_true]
    · subst hb
      refine WP.mono (WP.keep [] (Q := fun w => w = v) ?_ rfl) fun w ⟨hw, _⟩ => ?_
      · xrun
      · subst hw
        refine ⟨Keep.refl _ _, rfl, ?_⟩
        rw [h₁, hacc1, acc1V, ha1]; simp
  have Lw : Lay w F S := Lv.congr (kw.gpr (by decide)) kw.2.2 (by rw [hmw])
  have Rw : Rep w.mem F S V (upd W 34 (BitVec.ofNat 64 pos)) := hmw ▸ R1'
  have R2 := (Rw.wf G' (k := 33) (by decide) acc1).wf G' (k := 27) (by decide)
    (BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)))
  rw [show off F (8 * 33) = off F sAcc from rfl, show off F (8 * 27) = off F sL from rfl] at R2
  refine WP.mono (WP.keep [.rcx] (Q := fun x => x.mem = (w.mem.writeW (off F sAcc) acc1).writeW (off F sL)
      (BitVec.ofNat 64 (db - pos - 1 + (8 + H.D)))) ?_ rfl) fun x ⟨hmx, kx⟩ =>
    ⟨Lw.of_rep' Rw (hmx ▸ R2) (by simp [upd]) (kx.gpr (by decide)) kx.2.2,
      (hk.trans (kw.trans kx)).mono (by decide), hmx ▸ R2⟩
  xrun [ea_sp, Lw.rsp, Lw.st (d := sAcc) (by decide), Lw.st (d := sL) (by decide), haxw,
    (kw.gpr (by decide)).trans h₂, ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show 8 + H.D < 2 ^ 31 by omega)]
  rw [BitVec.ofNat_add_ofNat]

/-! ## `copyDb` and `verifyNb` -/

/-- `DB`, the `db` bytes at `e`, after `mHash` in `Y`. -/
theorem copyDb_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hcx : u.gpr .rcx = off S oY) (hdb1 : 1 ≤ db) (hfit : e + db ≤ oY) (hY : 8 + H.D + db ≤ 2048) :
    WP isa (copyDb H) u fun u' => Lay u' F S ∧ Keep [.rsi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => V (e + i)) (oY + (8 + H.D)) db) W := by
  have c7 : oY = 3584 := rfl
  have c5 : oRsa = 8192 := rfl
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8] (Q := fun v => v.gpr .rsi = off S e ∧
      v.gpr .r10 = BitVec.ofNat 64 db ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₁₀, h₂, hm⟩, hk⟩ => ?_)
  · xrun [copyDb, ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      R.rd (d := sEb) 23 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide), he, hdb]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (p := off S e) (o := oY) (disp := 8 + H.D) (n := db)
    (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀) hdb1 (by omega) h₁
    ((hk.gpr (by decide)).trans hcx) h₂ (fun i hi => by rw [off_plus]; exact Lv.sld8 (by omega))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV]
  split
  · rw [hm, off_plus, R.scr _ (by omega)]
  · rfl

include hH in
theorem verifyNb_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {db : Nat} (hdb : W 24 = BitVec.ofNat 64 db) (hdb2 : db ≤ 1024) :
    WP isa (.block (verifyNb H)) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      Rep u'.mem F S V (upd W 28 (BitVec.ofNat 64 ((db + (7 + H.D + H.P.L)) / H.P.B + 1))) := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have R1 := R.wf L.geo (k := 28) (by decide) (BitVec.ofNat 64 ((db + (7 + H.D + H.P.L)) / H.P.B + 1))
  rw [show off F (8 * 28) = off F sNb from rfl] at R1
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off F sNb)
      (BitVec.ofNat 64 ((db + (7 + H.D + H.P.L)) / H.P.B + 1))) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (k.gpr (by decide)) k.2.2, k, hm ▸ R1⟩
  have hsh : BitVec.ofNat 64 (db + (7 + H.D + H.P.L)) >>> lgB H = BitVec.ofNat 64 ((db + (7 + H.D + H.P.L)) / H.P.B) := by
    rw [shr_ofNat (lgB H) (by omega), hpow]
  xrun [verifyNb, ea_sp, L.rsp, L.ld (d := sDb) (by decide), L.st (d := sNb) (by decide),
    R.rd (d := sDb) 24 rfl (by decide), hdb, VG.Proof.MlKem.X86_64.sx_ofNat (show 7 + H.D + H.P.L < 2 ^ 31 by omega),
    BitVec.ofNat_add_ofNat, hsh, ofNat_add_lit, show 1 ≤ lgB H ∧ lgB H ≤ 63 from ⟨by omega, by omega⟩]

/-! ## `shift` -/

/-- The first `j` bytes from `base` replaced by those `d` after them, if `c`. -/
def shV (V : Nat → Byte) (c : Bool) (d base j : Nat) (x : Nat) : Byte :=
  if base ≤ x ∧ x < base + j then (if c then V (x + d) else V x) else V x

theorem and_one (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& 1 = BitVec.setWidth 64 (BitVec.ofBool (decide (a % 2 = 1))) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.and_one_is_mod]
  by_cases h : a % 2 = 1
  · simp [h]
  · have : a % 2 = 0 := by omega
    simp [this]

structure ShI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (c : Bool) (d base : Nat)
    (j : Nat) (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rcx, .rsi, .r11, .r9, .r8, .rax, .rdi] u₀ v
  rcx : v.gpr .rcx = off S base
  rsi : v.gpr .rsi = off S (base + d)
  r9 : v.gpr .r9 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool c)
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S (shV V c d base j) W

include hH in
theorem shiftPass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a d db : Nat} (ha : W 45 = BitVec.ofNat 64 a) (hd : W 46 = BitVec.ofNat 64 d)
    (hdb : W 24 = BitVec.ofNat 64 db) (ha' : a < 2 ^ 64) (hd1 : 1 ≤ d) (hdb1 : 1 ≤ db)
    (hfit : oY + 8 + H.D + db + d ≤ oRsa) :
    WP isa (shiftPass H) u fun u' => Lay u' F S ∧ Keep [.rcx, .rsi, .r11, .r9, .r10, .r8, .rax, .rdi] u u' ∧
      Rep u'.mem F S (shV V (decide (a % 2 = 1)) d (oY + 8 + H.D) db) W := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have c7 : oY = 3584 := rfl
  have c5 : oRsa = 8192 := rfl
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (WP.mono (WP.keep [.rcx, .rsi, .r11, .r9, .r10, .r8] (Q := fun v => v.gpr .rcx = off S (oY + 8 + H.D) ∧
      v.gpr .rsi = off S (oY + 8 + H.D + d) ∧ v.gpr .r9 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (a % 2 = 1))) ∧
      v.gpr .r10 = BitVec.ofNat 64 db ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₁₀, h₄, hm⟩, hk⟩ => ?_)
  · xrun [shiftPass, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY + 8 + H.D < 2 ^ 31 by omega), L.ld (d := sD) (by decide),
      L.ld (d := sA) (by decide), L.ld (d := sDb) (by decide), R.rd (d := sD) 46 rfl (by decide),
      R.rd (d := sA) 45 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide), ha, hd, hdb, off_plus]
    rw [and_one a ha']; rfl
  set c := decide (a % 2 = 1)
  set base := oY + 8 + H.D
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (byteLoop_ok (n := db) hdb1 (stepR_ok (by omega) v
      (show Reg.r10 ∉ [Reg.rcx, .rsi, .r11, .r9, .r8, .rax, .rdi] by decide) (by decide) h₁₀)
    (ShI v F S V W c d base) ?_ (u := v) ⟨Lv, Keep.refl _ _, h₁, h₂, h₃, h₄,
      hm ▸ (congrArg (fun V' => Rep u.mem F S V' W) (funext fun x => by
        simp only [shV, Nat.add_zero]; rw [ifn (by omega)])).mpr R⟩)
    fun w J => ⟨J.L, (hk.trans J.keep).mono (by decide), J.R⟩
  intro j hj w J
  have ea₁ : off S base + BitVec.ofNat 64 j = off S (base + j) := off_plus S base j
  have ea₂ : off S (base + d) + BitVec.ofNat 64 j = off S (base + j + d) := by
    rw [off_plus]; congr 1; omega
  have l₁ := J.L.sld8 (d := base + j) (by omega)
  have l₂ := J.L.sld8 (d := base + j + d) (by omega)
  have s₁ := J.L.sst8 (d := base + j) (by omega)
  have r₁ : w.mem (off S (base + j)) = V (base + j) := by
    rw [J.R.scr _ (by omega)]; simp only [shV]; rw [ifn (by omega)]
  have r₂ : w.mem (off S (base + j + d)) = V (base + j + d) := by
    rw [J.R.scr _ (by omega)]; simp only [shV]; rw [ifn (by omega)]
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
      w'.mem = w.mem.writeW (off S (base + j)) (if c then V (base + j + d) else V (base + j))) ?_ rfl)
    fun w' ⟨⟨h8, hm'⟩, hk'⟩ => ⟨(J.keep.trans hk').mono (by decide), h8, fun w'' k'' hm'' h8'' => ?_⟩
  · xrun [ea_ix0, J.rcx, J.rsi, J.r9, J.r8, ea₁, ea₂, l₁, l₂, s₁, r₁, r₂, sel_byte]
  · have R' := J.R.wb J.L.geo (o := base + j) (by omega) (if c then V (base + j + d) else V (base + j))
    rw [← hm', ← hm''] at R'
    have R'' : Rep w''.mem F S (shV V c d base (j + 1)) W := by
      refine (congrArg (fun V' => Rep w''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, shV]
      by_cases hx : x = base + j
      · subst hx; rw [ifp rfl, ifp (show base ≤ base + j ∧ base + j < base + (j + 1) by omega)]
      · rw [ifn hx]
        by_cases h' : base ≤ x ∧ x < base + j
        · rw [ifp h', ifp (show base ≤ x ∧ x < base + (j + 1) by omega)]
        · rw [ifn h', ifn (show ¬(base ≤ x ∧ x < base + (j + 1)) by omega)]
    exact ⟨J.L.of_rep J.R R'' (by rw [k''.gpr (by decide), hk'.gpr (by decide)]) (k''.2.2.trans hk'.2.2),
      (J.keep.trans (hk'.trans k'')).mono (by decide), by rw [k''.gpr (by decide), hk'.gpr (by decide), J.rcx],
      by rw [k''.gpr (by decide), hk'.gpr (by decide), J.rsi], by rw [k''.gpr (by decide), hk'.gpr (by decide), J.r9],
      h8'', R''⟩

theorem nextPass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a d j : Nat} (ha : W 45 = BitVec.ofNat 64 a) (hd : W 46 = BitVec.ofNat 64 d)
    (hj : W 44 = BitVec.ofNat 64 j) (ha' : a < 2 ^ 64) (hj1 : 1 ≤ j) (hj' : j < 2 ^ 64) :
    WP isa (.block nextPass) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      Rep u'.mem F S V (upd (upd (upd W 45 (BitVec.ofNat 64 (a / 2))) 46 (BitVec.ofNat 64 (2 * d))) 44
        (BitVec.ofNat 64 (j - 1))) ∧ u'.zf = some (decide (j - 1 = 0)) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 45) (by decide) (BitVec.ofNat 64 (a / 2))
  rw [show off F (8 * 45) = off F sA from rfl] at R1
  have R2 := R1.wf G' (k := 46) (by decide) (BitVec.ofNat 64 (2 * d))
  rw [show off F (8 * 46) = off F sD from rfl] at R2
  have R3 := R2.wf G' (k := 44) (by decide) (BitVec.ofNat 64 (j - 1))
  rw [show off F (8 * 44) = off F sJ from rfl] at R3
  have e46 : (u.mem.writeW (off F sA) (BitVec.ofNat 64 (a / 2))).readW (off F sD) 64 = BitVec.ofNat 64 d := by
    rw [R1.rd (d := sD) 46 rfl (by decide)]; simp [upd, hd]
  have e44 : ((u.mem.writeW (off F sA) (BitVec.ofNat 64 (a / 2))).writeW (off F sD) (BitVec.ofNat 64 (2 * d))).readW
      (off F sJ) 64 = BitVec.ofNat 64 j := by
    rw [R2.rd (d := sJ) 44 rfl (by decide)]; simp [upd, hj]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = ((u.mem.writeW (off F sA) (BitVec.ofNat 64 (a / 2))).writeW
      (off F sD) (BitVec.ofNat 64 (2 * d))).writeW (off F sJ) (BitVec.ofNat 64 (j - 1)) ∧
      u'.zf = some (decide (j - 1 = 0))) ?_ rfl)
    fun u' ⟨⟨hm, hz⟩, k⟩ => ⟨L.of_rep' R (hm ▸ R3) (by simp [upd]) (k.gpr (by decide)) k.2.2, k, hm ▸ R3, hz⟩
  have hsh : BitVec.ofNat 64 a >>> 1 = BitVec.ofNat 64 (a / 2) := by rw [shr_ofNat 1 ha']
  have hdd : BitVec.ofNat 64 d + BitVec.ofNat 64 d = BitVec.ofNat 64 (2 * d) := by
    rw [BitVec.ofNat_add_ofNat]; congr 1; omega
  xrun [nextPass, ea_sp, L.rsp, L.ld (d := sA) (by decide), L.st (d := sA) (by decide), L.ld (d := sD) (by decide),
    L.st (d := sD) (by decide), L.ld (d := sJ) (by decide), L.st (d := sJ) (by decide),
    R.rd (d := sA) 45 rfl (by decide), ha, hsh, e46, hdd, e44]
  have hj1' : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat hj1]
  rw [hj1', ofNat_beq_zero (by omega)]
  exact ⟨rfl, rfl⟩

/-- `shift`'s state after `p` passes, from `a₀ = pos + 1`. -/
structure PassI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (base db a₀ p : Nat)
    (w : State) : Prop where
  L : Lay w F S
  keep : Keep [.rax, .rcx, .rsi, .r11, .r9, .r10, .r8, .rdi] u₀ w
  rep : ∃ V' W', Rep w.mem F S V' W' ∧ W' 45 = BitVec.ofNat 64 (a₀ / 2 ^ p) ∧ W' 46 = BitVec.ofNat 64 (2 ^ p) ∧
    W' 44 = BitVec.ofNat 64 (10 - p) ∧ (∀ k < nW, k ≠ 44 → k ≠ 45 → k ≠ 46 → W' k = W k) ∧
    (∀ i < db, V' (base + i) = if i + a₀ % 2 ^ p < db then V (base + (i + a₀ % 2 ^ p)) else 0) ∧
    (∀ x, ¬ (base ≤ x ∧ x < base + db) → V' x = V x)

include hH in
/-- `DB`'s place in `Y` shifted left by `pos + 1` bytes, zeros after it. -/
theorem shift_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pos db : Nat} (hpos : W 34 = BitVec.ofNat 64 pos) (hdb : W 24 = BitVec.ofNat 64 db)
    (hp : pos + 1 < 1024) (hdb1 : 1 ≤ db) (hfit : 8 + H.D + db + 512 ≤ 2048)
    (hz : ∀ j, db ≤ j → j < db + 512 → V (oY + 8 + H.D + j) = 0) :
    WP isa (shift H) u fun u' => PassI u F S V W (oY + 8 + H.D) db (pos + 1) 10 u' := by
  have hDN := hH.hDN
  have hN := hH.N_le
  have c7 : oY = 3584 := rfl
  have c5 : oRsa = 8192 := rfl
  have G' := L.geo
  -- The first pass's slots.
  have R1 := R.wf G' (k := 45) (by decide) (BitVec.ofNat 64 (pos + 1))
  rw [show off F (8 * 45) = off F sA from rfl] at R1
  have R2 := R1.wf G' (k := 46) (by decide) (BitVec.ofNat 64 1)
  rw [show off F (8 * 46) = off F sD from rfl] at R2
  have R3 := R2.wf G' (k := 44) (by decide) (BitVec.ofNat 64 10)
  rw [show off F (8 * 44) = off F sJ from rfl] at R3
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v => v.mem = ((u.mem.writeW (off F sA) (BitVec.ofNat 64 (pos + 1))).writeW
      (off F sD) (BitVec.ofNat 64 1)).writeW (off F sJ) (BitVec.ofNat 64 10)) ?_ rfl) fun v ⟨hm, hk⟩ => ?_)
  · xrun [shift, ea_sp, L.rsp, L.ld (d := sPos) (by decide), R.rd (d := sPos) 34 rfl (by decide), hpos,
      L.st (d := sA) (by decide), L.st (d := sD) (by decide), L.st (d := sJ) (by decide), ofNat_add_lit]
    rfl
  have Rv : Rep v.mem F S V _ := hm ▸ R3
  have Lv : Lay v F S := L.of_rep' R Rv (by simp [upd]) (hk.gpr (by decide)) hk.2.2
  have I0 : PassI u F S V W (oY + 8 + H.D) db (pos + 1) 0 v :=
    ⟨Lv, hk.mono (by decide), V, _, Rv, by simp [upd], by simp [upd], by simp [upd],
      fun k _ h44 h45 h46 => by simp [upd, h44, h45, h46],
      fun i hi => by simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero]; rw [ifp hi], fun _ _ => rfl⟩
  refine WP.loop (M := isa) (fun n w => ∃ p, n = 10 - p ∧ p < 10 ∧ PassI u F S V W (oY + 8 + H.D) db (pos + 1) p w) ?_ (10 - 0) v
    ⟨0, rfl, by decide, I0⟩
  rintro n w ⟨p, rfl, hp10, I⟩
  obtain ⟨V', W', R', h45, h46, h44, hW', hV', hO'⟩ := I.rep
  have hpp : 2 ^ p ≤ 512 := by
    calc 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 512 := rfl
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hdbW : W' 24 = BitVec.ofNat 64 db := by rw [hW' 24 (by decide) (by decide) (by decide) (by decide), hdb]
  have ha' : (pos + 1) / 2 ^ p < 2 ^ 64 := by
    have := Nat.div_le_self (pos + 1) (2 ^ p); omega
  refine WP.seq (WP.mono (shiftPass_ok hH I.L R' h45 h46 hdbW ha' hp1 hdb1 (by omega)) fun x ⟨Lx, kx, Rx⟩ => ?_)
  refine WP.mono (nextPass_ok Lx Rx h45 h46 h44 ha' (by omega) (by omega)) fun y ⟨Ly, ky, Ry, hzy⟩ => ?_
  have I' : PassI u F S V W (oY + 8 + H.D) db (pos + 1) (p + 1) y := by
    refine ⟨Ly, (I.keep.trans (kx.trans ky)).mono (by decide), _, _, Ry, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    · simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]
      rw [Nat.pow_succ, Nat.mul_comm]
    · simp only [upd, ite_true]; congr 1
    · intro k hk h44 h45 h46
      simp only [upd, h44, h45, h46, ite_false]; exact hW' k hk h44 h45 h46
    · intro i hi
      have hm := Nat.mod_pow_succ (b := 2) (x := (pos + 1)) (k := p)
      simp only [shV, show (oY + 8 + H.D) ≤ (oY + 8 + H.D) + i ∧ (oY + 8 + H.D) + i < (oY + 8 + H.D) + db from ⟨by omega, by omega⟩, and_self, ite_true]
      by_cases hc : (pos + 1) / 2 ^ p % 2 = 1
      · rw [hc] at hm
        simp only [hc, decide_true, ite_true]
        by_cases hi' : i + 2 ^ p < db
        · rw [show (oY + 8 + H.D) + i + 2 ^ p = (oY + 8 + H.D) + (i + 2 ^ p) by omega, hV' _ hi', hm,
            show i + 2 ^ p + (pos + 1) % 2 ^ p = i + ((pos + 1) % 2 ^ p + 2 ^ p * 1) by omega]
        · rw [hO' _ (by omega), show (oY + 8 + H.D) + i + 2 ^ p = oY + 8 + H.D + (i + 2 ^ p) from by omega,
            hz _ (by omega) (by omega), ifn (show ¬ i + (pos + 1) % 2 ^ (p + 1) < db by omega)]
      · have hc0 : (pos + 1) / 2 ^ p % 2 = 0 := by omega
        rw [hc0] at hm
        simp only [hc, decide_false, Bool.false_eq_true, ite_false]
        rw [hV' i hi, hm, Nat.mul_zero]; simp only [Nat.add_zero]
    · intro x hx
      simp only [shV, hx, ite_false]; exact hO' x hx
  by_cases hend : p + 1 = 10
  · refine .inl ⟨by simp only [eval, hzy]; rw [show 10 - p - 1 = 0 by omega]; rfl, hend ▸ I'⟩
  · refine .inr ⟨by simp only [eval, hzy]; rw [decide_eq_false (by omega)]; rfl, 10 - (p + 1), by omega,
      p + 1, rfl, by omega, I'⟩

end VG.Proof.RsaPss.X86_64
