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

end VG.Proof.RsaPss.X86_64
