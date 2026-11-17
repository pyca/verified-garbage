module

import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Schedule
public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Rc4.Dword
public import VerifiedGarbage.Proof.Blowfish.Feistel

/-! ### `Blowfish.X86.Cipher`, which this module and modules that import it used -/

section

/-! ### `Blowfish.X86.F`, which only this module used -/

section

/-! ### `Blowfish.X86.Lookup`, which only this module used -/

section

/-!
# Blowfish on x86 (32-bit): an S-box lookup

`lookup_run`: `lookup sch j` leaves S-box `j`'s entry for xL's byte `3 - j`
(xL at `ebp + 16`) in `edi`, changing only the lookup's registers and the
flags.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- What a lookup needs: the schedule's address `S` at `esp + sch`, its S-boxes
readable, without wrapping around, and xL readable at `ebp + 16`. -/
structure LookEnv (sch : Nat) (S : BitVec 32) (s : State) : Prop where
  schRd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) sch) 4
  schVal : s.mem.readW (addr (s.gpr .esp) sch) 32 = S
  fit : S.toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 o) 4
  xl : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) xlOff) 4

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi]

theorem LookEnv.keep {sch : Nat} {S : BitVec 32} {s t : State} (E : LookEnv sch S s) {rs : List Reg}
    (h : Keep rs s t) (hm : t.mem = s.mem) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs) : LookEnv sch S t := by
  obtain r := keep_reads h
  refine ⟨?_, ?_, E.fit, fun o ho => ?_, ?_⟩
  · rw [r, h.gpr hsp]; exact E.schRd
  · rw [hm, h.gpr hsp]; exact E.schVal
  · rw [r]; exact E.rd o ho
  · rw [r, h.gpr hbp]; exact E.xl

/-! ## The index -/

theorem index_val (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (if j < 3 then (x >>> (8 * (3 - j))) &&& BitVec.ofNat 32 255 else x &&& BitVec.ofNat 32 255) =
      (quarter x j).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain h255 : (BitVec.ofNat 32 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  simp only [ite_true, ite_false, Nat.reduceLT, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, h255,
    Nat.reduceMul, Nat.reduceSub, hi, decide_true, Bool.true_and] <;>
  by_cases h8 : i < 8 <;> simp (disch := omega) [h8, BitVec.getLsbD_of_ge, Nat.add_comm]

theorem index_run (s : State) {j : Nat} (hj : j < 4) {x : BitVec 32}
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) xlOff) 4)
    (hx : s.mem.readW (addr (s.gpr .ebp) xlOff) 32 = x) :
    WP isa (.block (index j)) s fun t => t.gpr .esi = (quarter x j).setWidth 32 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [index, xlOff] at hr hx ⊢ <;> brun [hr, hx]

/-! ## Rotations selected by a bit of the index -/

/-- The bit `c` (1 or 2) of `q` clear. -/
def bitClr (q : BitVec 32) (c : Nat) : Bool := decide ((q &&& BitVec.ofNat 32 c).toNat < (1#32).toNat)

theorem sbb_mask (p : Bool) (x r : BitVec 32) :
    ((x ^^^ r) &&& (0#32 - BitVec.setWidth 32 (BitVec.ofBool p))) ^^^ r = if p then x else r := by
  rw [Proof.Rc4.borrow_mask32]
  cases p
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem condRot_run (s : State) (x : Reg) {c a : Nat} (ha1 : 1 ≤ a) (ha : a ≤ 31)
    (xc : x ≠ .ecx) (xd : x ≠ .edx) (xs : x ≠ .esi) :
    WP isa (.block (condRot x c a)) s fun t =>
      t.gpr x = (if bitClr (s.gpr .esi) c then s.gpr x else (s.gpr x).rotateRight a) ∧ t.mem = s.mem := by
  have cx : Reg.ecx ≠ x := Ne.symm xc
  have dx : Reg.edx ≠ x := Ne.symm xd
  have sx : Reg.esi ≠ x := Ne.symm xs
  unfold condRot
  brun [xc, xd, xs, cx, dx, sx, ha1, ha]
  rw [sbb_mask]
  rfl

theorem and_lane (q : BitVec 32) {L : Nat} (hL : q.toNat % 4 = L) {c : Nat} (hc : c = 1 ∨ c = 2) :
    q &&& BitVec.ofNat 32 c = BitVec.ofNat 32 L &&& BitVec.ofNat 32 c := by
  obtain e : q &&& BitVec.ofNat 32 3 = BitVec.ofNat 32 L := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (3 % 2 ^ 32 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_using [hL]
  obtain e' : ∀ d : BitVec 32, d = BitVec.ofNat 32 3 &&& d → q &&& d = BitVec.ofNat 32 L &&& d := by
    intro d hd
    conv => lhs; rw [hd]
    rw [← BitVec.and_assoc, e]
  rcases hc with rfl | rfl
  · exact e' _ (by decide)
  · exact e' _ (by decide)

theorem bitClr_lane (q : BitVec 32) {L : Nat} (hL : q.toNat % 4 = L) :
    bitClr q 1 = !decide (L % 2 = 1) ∧ bitClr q 2 = !decide (L / 2 = 1) := by
  obtain hl : L < 4 := by omega_using [hL]
  unfold bitClr
  rw [and_lane q hL (.inl rfl), and_lane q hL (.inr rfl)]
  rcases (by omega_using [hL] : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;> decide

theorem not_ite {α : Type} (b : Bool) (x y : α) : (if (!b) = true then x else y) = if b = true then y else x := by
  cases b <;> rfl

/-! ## The rows -/

theorem row_mask (q lm : BitVec 32) :
    (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (q.toNat < (4#32).toNat))) &&& lm) =
      if q.toNat < 4 then lm else 0 := by
  rw [Proof.Rc4.borrow_mask32, show (4#32).toNat = 4 from rfl]
  by_cases h : q.toNat < 4
  · simp only [h, decide_true, ite_true]; exact BitVec.allOnes_and
  · simp [h]

theorem row_run (u : State) {sch j : Nat} {q rp acc lm S : BitVec 32}
    (hsi : u.gpr .esi = q) (hdi : u.gpr .edi = acc) (hax : u.gpr .eax = lm) (hbx : u.gpr .ebx = rp)
    (hs : u.mem.readW (addr (u.gpr .esp) sch) 32 = S)
    (hrs : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) sch) 4)
    (hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (addr rp (planeOff j b)) 4) :
    WP isa (.block (row sch j)) u fun t =>
      let M := if q.toNat < 4 then lm else 0
      let w := fun b => u.mem.readW (addr rp (planeOff j b)) 32 &&& M
      t.gpr .edi = (((acc ||| w 0) ||| (w 1).rotateRight 24) ||| (w 2).rotateRight 16) |||
        (w 3).rotateRight 8 ∧
      t.gpr .esi = q - BitVec.ofNat 32 4 ∧ t.gpr .ebx = rp + BitVec.ofNat 32 4 ∧
      t.zf = some (S - (rp + BitVec.ofNat 32 4) - BitVec.ofNat 32 (2 ^ 32 - 256) == 0) ∧ t.mem = u.mem := by
  obtain r0 := hr 0 (by decide)
  obtain r1 := hr 1 (by decide)
  obtain r2 := hr 2 (by decide)
  obtain r3 := hr 3 (by decide)
  unfold row plane
  brun [hsi, hdi, hax, hbx, hs, hrs, r0, r1, r2, r3]
  simp only [row_mask, Nat.reduceMul, Nat.reduceSub]
theorem addr_row {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) {j b k : Nat} (hj : j < 4) (hb : b < 4)
    (hk : k < 64) :
    addr (S + BitVec.ofNat 32 (4 * k)) (planeOff j b) = S.setWidth 64 + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k) := by
  unfold addr
  rw [ofs_add, ← addr, addr_of_fit (by unfold planeOff; omega_using [fit, hj, hb, hk])]
  congr 2; unfold planeOff; omega_using []

/-- The lane mask, the accumulator and the row pointer. -/
theorem start_run (s : State) {sch : Nat} {S : BitVec 32} (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) sch) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) sch) 32 = S) {L : Nat} (hL : (s.gpr .esi).toNat % 4 = L) :
    WP isa (.block (lookupStart sch)) s fun t =>
      t.gpr .eax = laneMask L ∧ t.gpr .edi = 0 ∧ t.gpr .ebx = S ∧ t.mem = s.mem := by
  obtain hl : L < 4 := by omega_using [hL]
  obtain ⟨b1, b2⟩ := bitClr_lane _ hL
  unfold lookupStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain h0 : WP isa (.block [.mov .eax (imm 255)]) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 255 ∧ t.mem = s.mem := by brun
  refine WP.mono (WP.keep [.eax] h0 (by decide)) fun t₀ ⟨⟨t7, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (condRot_run t₀ .eax (c := 1) (a := 24) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide)) fun t₁ ⟨⟨u7, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (condRot_run t₁ .eax (c := 2) (a := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide)) fun t₂ ⟨⟨v7, vm⟩, vk⟩ => ?_
  obtain q1 : t₀.gpr .esi = s.gpr .esi := tk.gpr (by decide)
  obtain q2 : t₁.gpr .esi = s.gpr .esi := (uk.gpr (by decide)).trans q1
  obtain k2 : Keep [.eax, .ecx, .edx] s t₂ := ((tk.trans uk).trans vk).mono (by decide)
  obtain e7 : t₂.gpr .eax = laneMask L := by
    rw [v7, u7, q2, q1, t7, b1, b2, not_ite, not_ite]; exact laneMask_rot hl
  obtain em : t₂.mem = s.mem := by rw [vm, um, tm]
  obtain er : InRegions (t₂.rd ++ t₂.wr) (addr (t₂.gpr .esp) sch) 4 := by
    rw [keep_reads k2, k2.gpr (by decide)]; exact hr
  obtain ev : t₂.mem.readW (addr (t₂.gpr .esp) sch) 32 = S := by rw [em, k2.gpr (by decide)]; exact hv
  obtain ev' : s.mem.readW (addr (t₂.gpr .esp) sch) 32 = S := by rw [k2.gpr (by decide)]; exact hv
  brun [e7, em, er, ev, ev']

/-- After `k` rows of S-box `j` for the index `idx`, from the lookup's start `s₀`. -/
structure RowInv (s₀ : State) (S : BitVec 32) (j : Nat) (idx : Byte) (k : Nat) (u : State) : Prop where
  q : u.gpr .esi = idx.setWidth 32 - BitVec.ofNat 32 (4 * k)
  acc : u.gpr .edi = scanAcc s₀.mem (S.setWidth 64) j idx.toNat k
  lane : u.gpr .eax = laneMask (idx.toNat % 4)
  rp : u.gpr .ebx = S + BitVec.ofNat 32 (4 * k)
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

theorem row_step {sch : Nat} {S : BitVec 32} {s₀ : State} (E : LookEnv sch S s₀) {j : Nat} (hj : j < 4)
    (idx : Byte) {k : Nat} (hk : k < 64) {u : State} (I : RowInv s₀ S j idx k u) :
    WP isa (.block (row sch j)) u fun u' =>
      RowInv s₀ S j idx (k + 1) u' ∧ u'.zf = some (decide (k + 1 = 64)) := by
  have fit := E.fit
  obtain hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := keep_reads I.keep
  obtain hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (addr (S + BitVec.ofNat 32 (4 * k)) (planeOff j b)) 4 :=
    fun b hb => by rw [addr_row fit hj hb hk, hrd]; exact E.rd _ (by omega_using [hj, hk, hb])
  obtain hsp : u.gpr .esp = s₀.gpr .esp := I.keep.gpr (by decide)
  refine WP.mono (WP.keep [.ebx, .ecx, .edx, .esi, .edi] (row_run u (S := S) I.q I.acc I.lane I.rp
    (by rw [I.mem, hsp]; exact E.schVal) (by rw [hrd, hsp]; exact E.schRd) hr) (by
      simp [writesOnly, row, plane, Code.allInstrs, Taint.clobbers, Taint.dst, VG.Proof.MlDsa.X86.Pack.allRegs]))
    fun u' ⟨⟨a5, a4, a10, az, am⟩, ak⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, Keep.trans_sub I.keep ak (by decide), am.trans I.mem⟩, ?_⟩
  · rw [a4, BitVec.sub_sub, ← BitVec.ofNat_add]; congr 2
  · dsimp only at a5
    obtain e : ∀ q lm : BitVec 32, q = idx.setWidth 32 - BitVec.ofNat 32 (4 * k) →
        (if q.toNat < 4 then lm else 0) = if idx.toNat / 4 = k then lm else 0 := by
      intro q lm hq; subst hq
      have := row_hit idx hk
      by_cases h : idx.toNat / 4 = k
      · rw [ite_eq_left (this.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (this.mp h')), ite_eq_right h]
    rw [a5, e _ _ rfl, I.mem]
    simp only [addr_row fit hj (show 0 < 4 by decide) hk, addr_row fit hj (show 1 < 4 by decide) hk,
      addr_row fit hj (show 2 < 4 by decide) hk, addr_row fit hj (show 3 < 4 by decide) hk]
    exact scanAcc_succ _ _ _ _ _ _ rfl
  · rw [ak.gpr (by decide), I.lane]
  · rw [a10, ofs_add]; congr 2
  · rw [az, show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ofs_add, ofs_neg,
      ofNat_sub_beq' (by omega_using [hk]) (by decide)]
    congr 2; apply propext; omega_using [hk]

theorem rows_run {sch : Nat} {S : BitVec 32} {s₀ : State} (E : LookEnv sch S s₀) {j : Nat} (hj : j < 4)
    (idx : Byte) {u : State} (I : RowInv s₀ S j idx 0 u) :
    WP isa (.loop (.block (row sch j)) .ne) u (RowInv s₀ S j idx 64) := by
  refine WP.loop (M := isa) (Q := RowInv s₀ S j idx 64)
    (fun (n : Nat) (v : State) => ∃ k, k < 64 ∧ n = 64 - k ∧ RowInv s₀ S j idx k v) ?_ 64 u
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨k, hk, hn, J⟩
  refine WP.mono (row_step E hj idx hk J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : k + 1 = 64
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by simp [e], n - 1, by omega_using [hk, hn], k + 1, by omega_using [hk, e], by omega_using [hn], J'⟩

/-- The lookup of S-box `j` for byte `3 - j` of xL, `x`. -/
theorem lookup_run {sch : Nat} {S : BitVec 32} {s : State} (E : LookEnv sch S s) {j : Nat} (hj : j < 4)
    {x : BitVec 32} (hx : s.mem.readW (addr (s.gpr .ebp) xlOff) 32 = x) :
    WP isa (lookup sch j) s fun t =>
      t.gpr .edi = sEntry (scheduleAt s.mem (S.setWidth 64)) j (quarter x j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter x j
  unfold lookup
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.esi] (index_run s hj E.xl hx) (by
    unfold index; split <;> simp [writesOnly, Code.allInstrs, Taint.clobbers, Taint.dst,
      VG.Proof.MlDsa.X86.Pack.allRegs])) fun t ⟨⟨t4, tm⟩, tk⟩ => ?_
  obtain hL : (t.gpr .esi).toNat % 4 = idx.toNat % 4 := by rw [t4, BitVec.toNat_setWidth]; simp [idx]
  obtain Et := E.keep tk tm (by decide) (by decide)
  refine WP.mono (WP.keep [.eax, .ebx, .ecx, .edx, .edi] (start_run t Et.schRd Et.schVal hL) (by
      simp [writesOnly, lookupStart, condRot, Code.allInstrs, Taint.clobbers, Taint.dst,
        VG.Proof.MlDsa.X86.Pack.allRegs]))
    fun u ⟨⟨u7, u5, u10, um⟩, uk⟩ => ?_
  obtain K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  obtain I0 : RowInv s S j idx 0 u := by
    refine ⟨?_, by rw [u5, scanAcc_zero], u7, by rw [u10]; simp, K0, by rw [um]; exact tm⟩
    rw [uk.gpr (by decide), t4]; simp; rfl
  apply WP.seq
  refine WP.mono (rows_run E hj idx I0) fun v V => ?_
  unfold lookupEnd
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.ecx, .edx, .edi] (condRot_run v .edi (c := 1) (a := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide))
    fun w ⟨⟨w5, wm⟩, wk⟩ => ?_
  refine WP.mono (WP.keep [.ecx, .edx, .edi] (condRot_run w .edi (c := 2) (a := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide))
    fun y ⟨⟨y5, ym⟩, yk⟩ => ?_
  obtain hL4 : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨b1, b2⟩ := bitClr_lane _ (sub256_mod idx)
  refine ⟨?_, ((V.keep.trans wk).trans yk).mono (by decide), by rw [ym, wm, V.mem]⟩
  rw [y5, w5, wk.gpr (by decide), V.q, b1, b2, not_ite, not_ite, acc_rot _ hL4, V.acc, scanAcc_all]
  exact hitWord_ror _ _ hj idx

end VG.Proof.Blowfish.X86

end

end


/-!
# Blowfish on x86 (32-bit): F

`f_run`: F of xL (at `ebp + 16`) into `ebp + 24`, one S-box at a time (`fAcc`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- What F needs besides a lookup's: F's slot writable, apart from the
schedule, xL's slot and the schedule's address on the stack. -/
structure FEnv (sch : Nat) (S : BitVec 32) (s : State) : Prop extends LookEnv sch S s where
  fw : InRegions s.wr (addr (s.gpr .ebp) fOff) 4
  fS : Region.Disjoint ⟨addr (s.gpr .ebp) fOff, 4⟩ ⟨S.setWidth 64, 4168⟩
  fX : Mem.Sep (addr (s.gpr .ebp) xlOff) 4 (addr (s.gpr .ebp) fOff) 4
  fA : Mem.Sep (addr (s.gpr .esp) sch) 4 (addr (s.gpr .ebp) fOff) 4

theorem FEnv.keep {sch : Nat} {S : BitVec 32} {s t : State} (E : FEnv sch S s) {rs : List Reg}
    (h : Keep rs s t) (hm : t.mem = s.mem) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs) : FEnv sch S t :=
  { E.toLookEnv.keep h hm hsp hbp with
    fw := by rw [h.2.2, h.gpr hbp]; exact E.fw
    fS := by rw [h.gpr hbp]; exact E.fS
    fX := by rw [h.gpr hbp]; exact E.fX
    fA := by rw [h.gpr hbp, h.gpr hsp]; exact E.fA }

theorem sep_symm {a b : Addr} {n k : Nat} (h : Mem.Sep a n b k) : Mem.Sep b k a n :=
  fun x h₁ h₂ => h x h₂ h₁

/-- `FEnv` after a write of F's slot. -/
theorem FEnv.write {sch : Nat} {S : BitVec 32} {s t : State} (E : FEnv sch S s) {rs : List Reg} {v : BitVec 32}
    (h : Keep rs s t) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs)
    (hm : t.mem = s.mem.writeW (addr (s.gpr .ebp) fOff) (v : BitVec 32)) : FEnv sch S t := by
  obtain r := keep_reads h
  obtain esp := h.gpr hsp
  obtain ebp := h.gpr hbp
  refine ⟨⟨?_, ?_, E.fit, fun o ho => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [r, esp]; exact E.schRd
  · rw [hm, esp, Mem.readW_writeW_sep E.fA (by decide)]; exact E.schVal
  · rw [r]; exact E.rd o ho
  · rw [r, ebp]; exact E.xl
  · rw [h.2.2, ebp]; exact E.fw
  · rw [ebp]; exact E.fS
  · rw [ebp]; exact E.fX
  · rw [ebp, esp]; exact E.fA

theorem writeW_writeW32 (m : Mem) (a : Addr) (v v' : BitVec 32) :
    (m.writeW a v).writeW a v' = m.writeW a v' := by
  funext x
  simp only [Mem.writeW, Mem.write]
  split <;> rfl

/-- A write of F's slot leaves the schedule as it was. -/
theorem scheduleAt_writeF {S F : Addr} (h : Region.Disjoint ⟨F, 4⟩ ⟨S, 4168⟩) (m : Mem) (v : BitVec 32) :
    scheduleAt (m.writeW F v) S = scheduleAt m S :=
  scheduleAt_eq_of_frame S (rs := [⟨F, 4⟩])
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self F 4))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.symm)

theorem combine_run (u : State) {j : Nat} (hj : j < 4) (hw : InRegions u.wr (addr (u.gpr .ebp) fOff) 4) :
    WP isa (.block (combine j)) u fun t =>
      t.mem = u.mem.writeW (addr (u.gpr .ebp) fOff) (if j = 0 then u.gpr .edi
        else if j = 2 then u.mem.readW (addr (u.gpr .ebp) fOff) 32 ^^^ u.gpr .edi
        else u.mem.readW (addr (u.gpr .ebp) fOff) 32 + u.gpr .edi) := by
  obtain hr := region_in (rs := u.rd) hw
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [fOff] at hw hr ⊢ <;> brun [combine, hw, hr]

/-- S-box `j`'s lookup, then its accumulation into F's slot, which holds
`fAcc … (j - 1)` (or what it did, for `j = 0`). -/
theorem step_run {sch : Nat} {S : BitVec 32} {s₀ : State} (E : FEnv sch S s₀) {j : Nat} (hj : j < 4)
    {u : State} (k : Keep lookRegs s₀ u)
    (hm : u.mem = if j = 0 then s₀.mem else s₀.mem.writeW (addr (s₀.gpr .ebp) fOff)
      (fAcc (scheduleAt s₀.mem (S.setWidth 64)) (s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32) (j - 1)))
    {Q : State → Prop}
    (hQ : ∀ t, Keep lookRegs s₀ t → t.mem = s₀.mem.writeW (addr (s₀.gpr .ebp) fOff)
      (fAcc (scheduleAt s₀.mem (S.setWidth 64)) (s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32) j) → Q t) :
    WP isa (.seq (lookup sch j) (.block (combine j))) u Q := by
  obtain ebp : u.gpr .ebp = s₀.gpr .ebp := k.gpr (by decide)
  obtain Eu : FEnv sch S u := by
    by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte] at hm; exact E.keep k hm (by decide) (by decide)
    · simp only [h0, ↓reduceIte] at hm; exact E.write k (by decide) (by decide) hm
  obtain hx : u.mem.readW (addr (u.gpr .ebp) xlOff) 32 = s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32 := by
    rw [ebp, hm]; split
    · rfl
    · exact Mem.readW_writeW_sep E.fX (by decide)
  obtain hK : scheduleAt u.mem (S.setWidth 64) = scheduleAt s₀.mem (S.setWidth 64) := by
    rw [hm]; split
    · rfl
    · exact scheduleAt_writeF E.fS _ _
  apply WP.seq
  refine WP.mono (lookup_run Eu.toLookEnv hj hx) fun v ⟨v7, vk, vm⟩ => ?_
  obtain vbp : v.gpr .ebp = s₀.gpr .ebp := (vk.gpr (by decide)).trans ebp
  obtain hw : InRegions v.wr (addr (v.gpr .ebp) fOff) 4 := by rw [vk.2.2, vk.gpr (by decide)]; exact Eu.fw
  refine WP.mono (WP.keep [.ecx] (combine_run v hj hw) (by
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide))
    fun t ⟨tm, tk⟩ => hQ t ((k.trans vk).trans tk |>.mono (by decide)) ?_
  rw [tm, vm, vbp, v7, hK]
  -- For any `j`, with `fAcc_step`: a case split on `j` would have the kernel
  -- compare `fAcc … (1 - 1)` with `fAcc … 0` by evaluating the S-boxes.
  obtain hprev : 0 < j → u.mem.readW (addr (s₀.gpr .ebp) fOff) 32 =
      fAcc (scheduleAt s₀.mem (S.setWidth 64)) (s₀.mem.readW (addr (s₀.gpr .ebp) xlOff) 32) (j - 1) :=
    fun h => by
      rw [hm]; split
      · omega
      · exact Mem.readW_writeW_self32 _ _ _
  obtain hmem : ∀ v, u.mem.writeW (addr (s₀.gpr .ebp) fOff) v = s₀.mem.writeW (addr (s₀.gpr .ebp) fOff) v :=
    fun v => by
      rw [hm]; split
      · rfl
      · exact writeW_writeW32 _ _ _ _
  rw [hmem]
  exact congrArg _ (fAcc_step _ _ hj _ hprev)

theorem f_run {sch : Nat} {S : BitVec 32} {s : State} (E : FEnv sch S s) :
    WP isa (Impl.Blowfish.X86.f sch) s fun t =>
      Keep lookRegs s t ∧ t.mem = s.mem.writeW (addr (s.gpr .ebp) fOff)
        (Spec.Blowfish.f (scheduleAt s.mem (S.setWidth 64)) (s.mem.readW (addr (s.gpr .ebp) xlOff) 32)) := by
  unfold Impl.Blowfish.X86.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl fun t0 k0 m0 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0 m0 fun t1 k1 m1 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1 m1 fun t2 k2 m2 => ?_
  refine step_run E (j := 3) (by decide) k2 m2 fun t3 k3 m3 => ⟨k3, ?_⟩
  rw [m3, fAcc_three]

end VG.Proof.Blowfish.X86

end

end


/-!
# Blowfish on x86 (32-bit): the block function

`cipher_run`: `cipher sch up` takes the halves at `ebp + 16` and `ebp + 20`
to their encryption (`up`) or decryption under the schedule whose address is
at `esp + sch`, changing only `eax`–`edi` but `ebp`, the flags and the
working space's bytes 16–31.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- The P-array pointer's offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- Byte `d` of the working space at `B`. -/
abbrev slot (B : BitVec 32) (d : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 d

theorem addr_slot {B : BitVec 32} (h : B.toNat + 40 ≤ 2 ^ 32) {d : Nat} (hd : d < 40) :
    addr B d = slot B d := addr_of_fit (by omega_using [h, hd])

theorem slot_sep (B : BitVec 32) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 40) (he : e < 40) :
    Mem.Sep (slot B d) (32 / 8) (slot B e) (32 / 8) :=
  Offset.sep _ h (by omega_using [hd]) (by omega_using [he])

/-- What the block function needs: the working space (40 bytes) at `ebp`,
writable and apart from the schedule and the schedule's address, which is at
`esp + sch`. -/
structure CipherEnv (sch : Nat) (S B : BitVec 32) (s : State) : Prop where
  bp : s.gpr .ebp = B
  bfit : B.toNat + 40 ≤ 2 ^ 32
  bw : InRegions s.wr (B.setWidth 64) 40
  schRd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) sch) 4
  schVal : s.mem.readW (addr (s.gpr .esp) sch) 32 = S
  fit : S.toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 o) 4
  sepS : Region.Disjoint ⟨B.setWidth 64, 40⟩ ⟨S.setWidth 64, 4168⟩
  sepA : Region.Disjoint ⟨B.setWidth 64, 40⟩ ⟨addr (s.gpr .esp) sch, 4⟩

theorem CipherEnv.slotW {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {d : Nat}
    (hd : d + 4 ≤ 40) : InRegions s.wr (slot B d) 4 := inRegions_off E.bw hd

theorem CipherEnv.slotR {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {d : Nat}
    (hd : d + 4 ≤ 40) : InRegions (s.rd ++ s.wr) (slot B d) 4 := region_in (E.slotW hd)

/-- The working space's bytes are apart from the schedule's address. -/
theorem CipherEnv.argSep {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {d : Nat}
    (hd : d + 4 ≤ 40) : Mem.Sep (addr (s.gpr .esp) sch) 4 (slot B d) 4 :=
  E.sepA.symm.sep (Region.contains_self _ _) (Offset.contains_base _ hd (by omega_using [hd]))

theorem CipherEnv.frame {sch : Nat} {S B : BitVec 32} {s t : State} (E : CipherEnv sch S B s) {rs : List Reg}
    (h : Keep rs s t) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs)
    (hf : Frame [⟨B.setWidth 64, 40⟩] s.mem t.mem) : CipherEnv sch S B t := by
  obtain r := keep_reads h
  obtain esp := h.gpr hsp
  refine ⟨by rw [h.gpr hbp]; exact E.bp, E.bfit, by rw [h.2.2]; exact E.bw, by rw [r, esp]; exact E.schRd,
    ?_, E.fit, fun o ho => by rw [r]; exact E.rd o ho, E.sepS, by rw [esp]; exact E.sepA⟩
  rw [esp, hf.readW (Region.contains_self _ _) (fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact E.sepA.symm) (by decide)]
  exact E.schVal

/-- The schedule, after writes to the working space. -/
theorem CipherEnv.sched {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {m : Mem}
    (hf : Frame [⟨B.setWidth 64, 40⟩] s.mem m) : scheduleAt m (S.setWidth 64) = scheduleAt s.mem (S.setWidth 64) :=
  scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact E.sepS.symm

theorem CipherEnv.fenv {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) : FEnv sch S s where
  schRd := E.schRd
  schVal := E.schVal
  fit := E.fit
  rd := E.rd
  xl := by rw [E.bp, addr_slot E.bfit (by decide)]; exact E.slotR (by decide)
  fw := by rw [E.bp, addr_slot E.bfit (by decide)]; exact E.slotW (by decide)
  fS := by
    rw [E.bp, addr_slot E.bfit (by decide)]
    exact E.sepS.sub_left (Offset.sub_base _ (by decide))
  fX := by rw [E.bp, addr_slot E.bfit (by decide), addr_slot E.bfit (by decide)]; exact slot_sep B (by decide) (by decide) (by decide)
  fA := by rw [E.bp, addr_slot E.bfit (by decide)]; exact E.argSep (by decide)

theorem round_head (u : State) (up : Bool) {B Pp P : BitVec 32} {a : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4)
    (r28 : InRegions (u.rd ++ u.wr) (slot B 28) 4) (hpp : u.mem.readW (slot B 28) 32 = Pp)
    (ha : addr Pp (pAt up) = a) (hra : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
        .mov .eax (.mem (at_ .ebp xlOff)), .alu .xor .eax (.reg .ecx), .store (at_ .ebp xlOff) .eax]) u
      fun t => t.mem = u.mem.writeW (slot B 16) (u.mem.readW (slot B 16) 32 ^^^ P) := by
  obtain r16 := region_in (rs := u.rd) w16
  rw [← ha] at hra hP
  brun [hb, addr_slot bfit, hpp, w16, r16, r28, hra, hP]

/-- Slot 28 and the schedule's address, past the tail's writes of the halves. -/
theorem readW_past2 {m : Mem} {B : BitVec 32} {a : Addr} {n : Nat} (h20 : Mem.Sep a (n / 8) (slot B 20) 4)
    (h16 : Mem.Sep a (n / 8) (slot B 16) 4) (hn : n / 8 < 2 ^ 64) (x y : BitVec 32) :
    ((m.writeW (slot B 20) x).writeW (slot B 16) y).readW a n = m.readW a n := by
  rw [Mem.readW_writeW_sep h16 hn, Mem.readW_writeW_sep h20 hn]

theorem pBase_succ (S : BitVec 32) (up : Bool) {i : Nat} (hi : i < 16) :
    (if up then S + BitVec.ofNat 32 (pBase up i) + 4#32 else S + BitVec.ofNat 32 (pBase up i) - 4#32) =
      S + BitVec.ofNat 32 (pBase up (i + 1)) := by
  cases up
  · simp only [Bool.false_eq_true, ite_false, pBase]
    exact (ofs_sub S (a := 4160 - 4 * i) (b := 4) (by omega_using [hi])).trans (by congr 2)
  · simp only [ite_true, pBase]
    exact (ofs_add S _ 4).trans (by congr 2)

theorem pBase_end (S : BitVec 32) (up : Bool) {i : Nat} (hi : i < 16) :
    (S - (S + BitVec.ofNat 32 (pBase up (i + 1))) - BitVec.ofNat 32 (2 ^ 32 - if up then pOff + 64 else pOff)
      == 0) = decide (i + 1 = 16) := by
  cases up <;> simp only [pBase, pOff, Bool.false_eq_true, ite_false, ite_true] <;>
  · rw [ofs_neg, ofNat_sub_beq' (by omega_using [hi]) (by decide)]
    congr 1; apply propext; omega_arith

theorem round_tail (u : State) (up : Bool) {sch : Nat} {B S : BitVec 32} {i : Nat} (hi : i < 16)
    (hb : u.gpr .ebp = B) (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4)
    (w20 : InRegions u.wr (slot B 20) 4) (w24 : InRegions u.wr (slot B 24) 4)
    (w28 : InRegions u.wr (slot B 28) 4)
    (hrs : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) sch) 4)
    (hs : u.mem.readW (addr (u.gpr .esp) sch) 32 = S)
    (hA : ∀ d, d + 4 ≤ 40 → Mem.Sep (addr (u.gpr .esp) sch) 4 (slot B d) 4)
    (hpp : u.mem.readW (slot B 28) 32 = S + BitVec.ofNat 32 (pBase up i)) :
    WP isa (.block [.mov .eax (.mem (at_ .ebp xrOff)), .alu .xor .eax (.mem (at_ .ebp fOff)),
        .mov .ecx (.mem (at_ .ebp xlOff)), .store (at_ .ebp xrOff) .ecx, .store (at_ .ebp xlOff) .eax,
        .mov .ebx (.mem (at_ .ebp ppOff)), .alu (if up then .add else .sub) .ebx (imm 4),
        .store (at_ .ebp ppOff) .ebx, .mov .ecx (.mem (at_ .esp sch)), .alu .sub .ecx (.reg .ebx),
        .alu .cmp .ecx (imm (2 ^ 32 - if up then pOff + 64 else pOff))]) u fun t =>
      t.mem = ((u.mem.writeW (slot B 20) (u.mem.readW (slot B 16) 32)).writeW (slot B 16)
        (u.mem.readW (slot B 20) 32 ^^^ u.mem.readW (slot B 24) 32)).writeW (slot B 28)
          (S + BitVec.ofNat 32 (pBase up (i + 1))) ∧
      t.zf = some (decide (i + 1 = 16)) := by
  obtain r16 := region_in (rs := u.rd) w16
  obtain r20 := region_in (rs := u.rd) w20
  obtain r24 := region_in (rs := u.rd) w24
  obtain r28 := region_in (rs := u.rd) w28
  obtain e28 := fun x y => readW_past2 (m := u.mem) (a := slot B 28) (n := 32)
    (slot_sep B (by decide) (by decide) (by decide)) (slot_sep B (by decide) (by decide) (by decide)) (by decide) x y
  obtain eA := fun x y => readW_past2 (m := u.mem) (a := addr (u.gpr .esp) sch) (n := 32)
    (hA 20 (by decide)) (hA 16 (by decide)) (by decide) x y
  obtain eA' : ∀ m : Mem, ∀ x : BitVec 32, (m.writeW (slot B 28) x).readW (addr (u.gpr .esp) sch) 32 =
      m.readW (addr (u.gpr .esp) sch) 32 := fun m x => Mem.readW_writeW_sep (hA 28 (by decide)) (by decide)
  obtain hp := pBase_succ S up hi
  obtain he := pBase_end S up hi
  cases up <;>
  · brun [hb, addr_slot bfit, w16, w20, w28, r16, r20, r24, r28, hrs, e28, eA, eA', hs, hpp]
    simp only [ite_false, ite_true, Bool.false_eq_true] at hp he
    rw [hp, he]; exact ⟨rfl, rfl⟩

/-- The address of the P-array entry of round `i`. -/
theorem addr_P {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) {i : Nat} (hi : i < 16) :
    addr (S + BitVec.ofNat 32 (pBase up i)) (pAt up) = S.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * ord up i) := by
  unfold addr
  rw [ofs_add, ← addr, addr_of_fit (by cases up <;> simp [pBase, pAt] <;> omega_arith)]
  congr 2; cases up <;> simp [pBase, pAt, ord] <;> omega_using [hi]

/-- The bytes the block function writes: the halves, F and the P-array pointer. -/
abbrev cRegion (B : BitVec 32) : List Region := [⟨slot B 16, 16⟩]

theorem frame_slot {m m' : Mem} {B : BitVec 32} (h : Frame (cRegion B) m m') {d : Nat} (hd : 16 ≤ d)
    (hd' : d + 4 ≤ 32) (v : BitVec 32) : Frame (cRegion B) m (m'.writeW (slot B d) v) :=
  h.writeW (List.mem_singleton_self _) _ (Offset.contains _ hd hd' (by omega_using []))

theorem frame_wide {m m' : Mem} {B : BitVec 32} (h : Frame (cRegion B) m m') :
    Frame [⟨B.setWidth 64, 40⟩] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

/-- After `i` rounds from `s₀`. -/
structure CInv (sch : Nat) (S B : BitVec 32) (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  env : CipherEnv sch S B u
  pp : u.mem.readW (slot B 28) 32 = S + BitVec.ofNat 32 (pBase up i)
  halves : (u.mem.readW (slot B 16) 32, u.mem.readW (slot B 20) 32) =
    iter (scheduleAt s₀.mem (S.setWidth 64)) (ord up) i (s₀.mem.readW (slot B 16) 32, s₀.mem.readW (slot B 20) 32)
  keep : Keep lookRegs s₀ u
  frame : Frame (cRegion B) s₀.mem u.mem

theorem round_step {sch : Nat} {S B : BitVec 32} {s₀ : State} (E : CipherEnv sch S B s₀) (up : Bool) {i : Nat}
    (hi : i < 16) {u : State} (I : CInv sch S B s₀ up i u) :
    WP isa (round sch up) u fun u' => CInv sch S B s₀ up (i + 1) u' ∧ u'.zf = some (decide (i + 1 = 16)) := by
  have Eu := I.env
  have fit := E.fit
  have bfit := E.bfit
  obtain ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega_arith
  let K := scheduleAt s₀.mem (S.setWidth 64)
  obtain hK : scheduleAt u.mem (S.setWidth 64) = K := E.sched (frame_wide I.frame)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ebx, .ecx] (round_head u up (P := pEntry K (ord up i)) Eu.bp bfit
    (Eu.slotW (by decide)) (Eu.slotR (by decide)) I.pp (addr_P fit up hi) (Eu.rd _ (by omega_using [ho]))
    (by rw [← pEntry_read _ _ ho, hK])) (by cases up <;> decide)) fun v ⟨vm, vk⟩ => ?_
  obtain fv : Frame (cRegion B) s₀.mem v.mem := by rw [vm]; exact frame_slot I.frame (by decide) (by decide) _
  obtain Ev : CipherEnv sch S B v := Eu.frame vk (by decide) (by decide) (by
    rw [vm]; exact frame_wide (frame_slot (Frame.refl _ _) (by decide) (by decide) _))
  apply WP.seq
  refine WP.mono (f_run Ev.fenv) fun w ⟨wk, wm⟩ => ?_
  rw [Ev.bp, addr_slot bfit (by decide), addr_slot bfit (by decide), E.sched (frame_wide fv)] at wm
  simp only [fOff, xlOff] at wm
  obtain fw : Frame (cRegion B) s₀.mem w.mem := by rw [wm]; exact frame_slot fv (by decide) (by decide) _
  obtain Ew : CipherEnv sch S B w := Ev.frame wk (by decide) (by decide) (by
    rw [wm]; exact frame_wide (frame_slot (Frame.refl _ _) (by decide) (by decide) _))
  -- The slots after the head and F.
  obtain v16 : v.mem.readW (slot B 16) 32 = u.mem.readW (slot B 16) 32 ^^^ pEntry K (ord up i) := by
    rw [vm, Mem.readW_writeW_self32]
  obtain w16 : w.mem.readW (slot B 16) 32 = u.mem.readW (slot B 16) 32 ^^^ pEntry K (ord up i) := by
    rw [wm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), v16]
  obtain w20 : w.mem.readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 := by
    rw [wm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), vm,
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide)]
  obtain w24 : w.mem.readW (slot B 24) 32 = f K (u.mem.readW (slot B 16) 32 ^^^ pEntry K (ord up i)) := by
    rw [wm, Mem.readW_writeW_self32, v16]
  obtain w28 : w.mem.readW (slot B 28) 32 = S + BitVec.ofNat 32 (pBase up i) := by
    rw [wm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), vm,
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), I.pp]
  refine WP.mono (WP.keep [.eax, .ebx, .ecx] (round_tail w up hi Ew.bp bfit (Ew.slotW (by decide))
    (Ew.slotW (by decide)) (Ew.slotW (by decide)) (Ew.slotW (by decide)) Ew.schRd Ew.schVal
    (fun d hd => Ew.argSep hd) w28) (by
      cases up <;> simp [writesOnly, Code.allInstrs, Taint.clobbers, Taint.dst, VG.Proof.MlDsa.X86.Pack.allRegs])) fun x ⟨⟨xm, xz⟩, xk⟩ => ?_
  obtain fx : Frame (cRegion B) s₀.mem x.mem := by
    rw [xm]
    exact frame_slot (frame_slot (frame_slot fw (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _
  obtain Ex : CipherEnv sch S B x := Ew.frame xk (by decide) (by decide) (by
    rw [xm]
    exact frame_wide (frame_slot (frame_slot (frame_slot (Frame.refl _ _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _))
  refine ⟨⟨by omega_using [hi], Ex, by rw [xm, Mem.readW_writeW_self32], ?_, (((I.keep.trans vk).trans wk).trans xk).mono (by decide), fx⟩, xz⟩
  obtain x16 : x.mem.readW (slot B 16) 32 = w.mem.readW (slot B 20) 32 ^^^ w.mem.readW (slot B 24) 32 := by
    rw [xm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  obtain x20 : x.mem.readW (slot B 20) 32 = w.mem.readW (slot B 16) 32 := by
    rw [xm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  rw [x16, x20, w16, w20, w24, iter_succ, ← I.halves]
  simp only [roundStep]
  rw [BitVec.xor_comm]

theorem cipher_start (u : State) (up : Bool) {sch : Nat} {B S : BitVec 32} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w28 : InRegions u.wr (slot B 28) 4)
    (hrs : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) sch) 4)
    (hs : u.mem.readW (addr (u.gpr .esp) sch) 32 = S) :
    WP isa (.block [.mov .ebx (.mem (at_ .esp sch)), .alu .add .ebx (imm (if up then pOff else pOff + 64)),
        .store (at_ .ebp ppOff) .ebx]) u fun t =>
      t.mem = u.mem.writeW (slot B 28) (S + BitVec.ofNat 32 (pBase up 0)) := by
  cases up <;> brun [hb, addr_slot bfit, w28, hrs, hs, pOff, pBase]

theorem rounds_run {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) (up : Bool) {u : State}
    (I : CInv sch S B s up 0 u) : WP isa (.loop (round sch up) .ne) u (CInv sch S B s up 16) := by
  refine WP.loop (M := isa) (Q := CInv sch S B s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv sch S B s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : i + 1 = 16
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], n - 1, by omega_using [hi, hn], i + 1, by omega_using [hi, e], by omega_using [hn], J'⟩

/-- The addresses of the last P-array entries. -/
theorem addr_last {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) :
    addr (S + BitVec.ofNat 32 (pBase up 16)) (pAt up) = S.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * ord up 16) ∧
      addr (S + BitVec.ofNat 32 (pBase up 16)) (4 - pAt up) =
        S.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * ord up 17) := by
  constructor <;>
  · unfold addr
    rw [ofs_add, ← addr, addr_of_fit (by cases up <;> simp [pBase, pAt] <;> omega_using [fit])]
    congr 2; cases up <;> simp [pBase, pAt, ord]

theorem cipher_end (u : State) (up : Bool) {B Pp P₁₆ P₁₇ : BitVec 32} {a b : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4) (w20 : InRegions u.wr (slot B 20) 4)
    (r28 : InRegions (u.rd ++ u.wr) (slot B 28) 4) (hpp : u.mem.readW (slot B 28) 32 = Pp)
    (ha : addr Pp (pAt up) = a) (hb' : addr Pp (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
        .alu .xor .ecx (.mem (at_ .ebp xlOff)), .mov .eax (.mem (at_ .ebx (4 - pAt up))),
        .alu .xor .eax (.mem (at_ .ebp xrOff)), .store (at_ .ebp xlOff) .eax,
        .store (at_ .ebp xrOff) .ecx]) u fun t =>
      t.mem = (u.mem.writeW (slot B 16) (P₁₇ ^^^ u.mem.readW (slot B 20) 32)).writeW (slot B 20)
        (P₁₆ ^^^ u.mem.readW (slot B 16) 32) := by
  obtain r16 := region_in (rs := u.rd) w16
  obtain r20 := region_in (rs := u.rd) w20
  rw [← ha] at hra h16
  rw [← hb'] at hrb h17
  brun [hb, addr_slot bfit, hpp, w16, w20, r16, r20, r28, hra, hrb, h16, h17]

/-- The block function. -/
theorem cipher_run {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) (up : Bool) :
    WP isa (cipher sch up) s fun t =>
      (t.mem.readW (slot B 16) 32, t.mem.readW (slot B 20) 32) =
        feistel (scheduleAt s.mem (S.setWidth 64)) (ord up) (s.mem.readW (slot B 16) 32)
          (s.mem.readW (slot B 20) 32) ∧
      Keep lookRegs s t ∧ Frame (cRegion B) s.mem t.mem := by
  have fit := E.fit
  have bfit := E.bfit
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.ebx] (cipher_start s up E.bp bfit (E.slotW (by decide)) E.schRd E.schVal) (by
    cases up <;> simp [writesOnly, Code.allInstrs, Taint.clobbers, Taint.dst, VG.Proof.MlDsa.X86.Pack.allRegs]))
    fun u ⟨um, uk⟩ => ?_
  obtain fu : Frame (cRegion B) s.mem u.mem := by rw [um]; exact frame_slot (Frame.refl _ _) (by decide) (by decide) _
  obtain I0 : CInv sch S B s up 0 u := by
    refine ⟨by decide, E.frame uk (by decide) (by decide) (frame_wide fu), by rw [um, Mem.readW_writeW_self32], ?_,
      uk.mono (by decide), fu⟩
    rw [um, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide)]
    rfl
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  obtain ⟨a16, a17⟩ := addr_last fit up
  have Ev := V.env
  let K := scheduleAt s.mem (S.setWidth 64)
  obtain hK : scheduleAt v.mem (S.setWidth 64) = K := E.sched (frame_wide V.frame)
  obtain r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  obtain r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  obtain o16 : ord up 16 < 18 := by cases up <;> decide
  obtain o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.eax, .ebx, .ecx] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) Ev.bp bfit (Ev.slotW (by decide)) (Ev.slotW (by decide))
    (Ev.slotR (by decide)) V.pp a16 a17 (Ev.rd _ r16) (Ev.rd _ r17)
    (by rw [← pEntry_read _ _ o16, hK]) (by rw [← pEntry_read _ _ o17, hK])) (by
      cases up <;> decide))
    fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans tk).mono (by decide), by
    rw [tm]; exact frame_slot (frame_slot V.frame (by decide) (by decide) _) (by decide) (by decide) _⟩
  rw [tm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32, Mem.readW_writeW_self32, feistel_eq, ← V.halves, BitVec.xor_comm,
    BitVec.xor_comm (pEntry _ _)]

end VG.Proof.Blowfish.X86

end

end

/-!
# Blowfish on x86 (32-bit): ECB

`ecb_correct`: every block becomes its encryption or decryption, one at a
time; our caller's registers are saved in the working space and restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## Blocks in and out of the halves -/

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega_arith | (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

theorem bswap_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (bswap x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact bswap_bit x hb hi

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem bswap_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    bswap (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [bswap_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega_arith),
    ← Mem.readW_byte m _ (by omega_arith), Offset.add_add]

/-- The block at the data pointer (in the working space) into the halves. -/
theorem loadBlock_run (u : State) {B P : BitVec 32} {Pa : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4) (w20 : InRegions u.wr (slot B 20) 4)
    (r32 : InRegions (u.rd ++ u.wr) (slot B 32) 4) (hP : u.mem.readW (slot B 32) 32 = P)
    (e0 : addr P 0 = Pa) (e4 : addr P 4 = Pa + BitVec.ofNat 64 4)
    (r0 : InRegions (u.rd ++ u.wr) Pa 4) (r4 : InRegions (u.rd ++ u.wr) (Pa + BitVec.ofNat 64 4) 4)
    (sep : Mem.Sep (Pa + BitVec.ofNat 64 4) (32 / 8) (slot B 16) (32 / 8)) :
    WP isa (.block loadBlock) u fun t =>
      t.mem = (u.mem.writeW (slot B 16) (decodeWord (blockAt u.mem Pa) 0)).writeW (slot B 20)
        (decodeWord (blockAt u.mem Pa) 4) := by
  obtain l0 := bswap_load u.mem Pa (o := 0) (by decide)
  obtain l4 := bswap_load u.mem Pa (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  obtain e : ∀ v : BitVec 32, (u.mem.writeW (slot B 16) v).readW (Pa + BitVec.ofNat 64 4) 32 =
      u.mem.readW (Pa + BitVec.ofNat 64 4) 32 := fun v => Mem.readW_writeW_sep sep (by decide)
  unfold loadBlock
  brun [hb, addr_slot bfit, w16, w20, r32, hP, e0, e4, r0, r4, e, l0, l4]

/-- The halves to the block at the data pointer, the next block's pointer,
and the counter less one. -/
theorem storeBlock_run (u : State) {B P C : BitVec 32} {Pa : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (r16 : InRegions (u.rd ++ u.wr) (slot B 16) 4)
    (r20 : InRegions (u.rd ++ u.wr) (slot B 20) 4) (w32 : InRegions u.wr (slot B 32) 4)
    (w36 : InRegions u.wr (slot B 36) 4) (hP : u.mem.readW (slot B 32) 32 = P)
    (hC : u.mem.readW (slot B 36) 32 = C) (e0 : addr P 0 = Pa) (e4 : addr P 4 = Pa + BitVec.ofNat 64 4)
    (w0 : InRegions u.wr Pa 4) (w4 : InRegions u.wr (Pa + BitVec.ofNat 64 4) 4)
    (sep : Mem.Sep (slot B 20) (32 / 8) Pa (32 / 8)) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (((u.mem.writeW Pa (bswap (u.mem.readW (slot B 16) 32))).writeW (Pa + BitVec.ofNat 64 4)
          (bswap (u.mem.readW (slot B 20) 32))).writeW (slot B 32) (P + BitVec.ofNat 32 8)).writeW (slot B 36)
          (C - BitVec.ofNat 32 1) ∧
        t.zf = some (C - BitVec.ofNat 32 1 == 0) := by
  obtain r32 := region_in (rs := u.rd) w32
  obtain r36 := region_in (rs := u.rd) w36
  obtain e : ∀ v : BitVec 32, (u.mem.writeW Pa v).readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 :=
    fun v => Mem.readW_writeW_sep sep (by decide)
  unfold storeBlock
  brun [hb, addr_slot bfit, r16, r20, r32, r36, w32, w36, hP, hC, e0, e4, w0, w4, e]

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply fun h' => h x (Region.contains_self _ _) ((Region.contains_self a 4).byte h')

/-- What the stores leave: the block's bytes, the pointer and the counter. -/
theorem stored_facts (m : Mem) (B : BitVec 32) (Pa : Addr) (L R P C : BitVec 32)
    (dj : Region.Disjoint ⟨slot B 32, 8⟩ ⟨Pa, 8⟩) :
    let M := (((m.writeW Pa (bswap L)).writeW (Pa + BitVec.ofNat 64 4) (bswap R)).writeW (slot B 32) P).writeW
      (slot B 36) C
    M.readW (slot B 32) 32 = P ∧ M.readW (slot B 36) 32 = C ∧
      Frame [⟨Pa, 8⟩, ⟨slot B 32, 8⟩] m M ∧ blockAt M Pa = encodeBlock L R := by
  intro M
  refine ⟨by rw [Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _, ?_, ?_⟩
  · have c0 : Region.Contains ⟨Pa, 8⟩ Pa (32 / 8) := Offset.contains_base Pa (d := 0) (n := 4) (k := 8)
      (by decide) (by decide) |> fun h => by rwa [BitVec.add_zero] at h
    obtain c4 : Region.Contains ⟨Pa, 8⟩ (Pa + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base Pa (by decide) (by decide)
    obtain c32 : Region.Contains ⟨slot B 32, 8⟩ (slot B 32) (32 / 8) :=
      Offset.contains (e := 32) (k := 8) (d := 32) (n := 4) _ (by decide) (by decide) (by decide)
    obtain c36 : Region.Contains ⟨slot B 32, 8⟩ (slot B 36) (32 / 8) :=
      Offset.contains (e := 32) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide) (by decide)
    exact ((((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ c32).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ c36
  · refine blockAt_eq _ _ _ fun i hi => ?_
    obtain dk : ∀ o, o < 8 → Region.Disjoint ⟨Pa + BitVec.ofNat 64 o, 1⟩ ⟨slot B 32, 8⟩ :=
      fun o ho => (dj.sub_right (Offset.sub_base Pa (d := o) (n := 1) (k := 8) (by omega_arith))).symm
    obtain d32 := (dk i hi).sub_right (Offset.sub (e := 32) (k := 8) (d := 32) (n := 4) (B.setWidth 64)
      (by decide) (by decide))
    obtain d36 := (dk i hi).sub_right (Offset.sub (e := 32) (k := 8) (d := 36) (n := 4) (B.setWidth 64)
      (by decide) (by decide))
    simp only [M]
    rw [writeW32_other _ d36, writeW32_other _ d32, encodeBlock_getD _ _ hi]
    by_cases h4 : i < 4
    · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint Pa (d := i) (n := 1) (e := 4) (k := 4) (by omega_arith)
        (by omega_arith) (by decide)), st_byte _ _ _ h4, bswap_byte _ h4]
    · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega_arith, ← Offset.add_add, st_byte _ _ _ (by omega_arith),
        bswap_byte _ (by omega_arith)]
      congr 2; omega_arith

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The schedule, the data, the working space and the arguments of `s`. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 4168⟩
abbrev dataR (s : State) : Region := ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
abbrev scrR (s : State) : Region := ⟨(arg s 3).setWidth 64, 256⟩
abbrev argR (s : State) : Region := ⟨argAddr s 0, 16⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

/-- What ECB may assume: the schedule and the arguments readable, the `n`
blocks and the working space writable, apart, none wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [schR s, argR s]
  wr : s.wr = [dataR s, scrR s]
  kd : (schR s).Disjoint (dataR s)
  kb : (schR s).Disjoint (scrR s)
  db : (dataR s).Disjoint (scrR s)
  ad : (argR s).Disjoint (dataR s)
  ab : (argR s).Disjoint (scrR s)
  retD : (retR s).Disjoint (dataR s)
  retB : (retR s).Disjoint (scrR s)
  fK : (arg s 0).toNat + 4168 ≤ 2 ^ 32
  fD : (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 256 ≤ 2 ^ 32
  fsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` (of `s₀`) in the working space at `B`. -/
def Saved (m : Mem) (B : BitVec 32) (s₀ : State) : Prop :=
  m.readW (slot B 0) 32 = s₀.gpr .ebx ∧ m.readW (slot B 4) 32 = s₀.gpr .esi ∧
    m.readW (slot B 8) 32 = s₀.gpr .edi ∧ m.readW (slot B 12) 32 = s₀.gpr .ebp

/-- The saved registers survive writes outside their 16 bytes. -/
theorem Saved.frame {m m' : Mem} {B : BitVec 32} {s₀ : State} {rs : List Region} (h : Saved m B s₀)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨B.setWidth 64, 16⟩ r) : Saved m' B s₀ := by
  have e (d : Nat) (hd' : d + 4 ≤ 16) : m'.readW (slot B d) 32 = m.readW (slot B d) 32 :=
    hf.readW (Offset.contains_base _ hd' (by omega_arith)) hd (by decide)
  obtain ⟨h0, h4, h8, h12⟩ := h
  exact ⟨(e 0 (by decide)).trans h0, (e 4 (by decide)).trans h4, (e 8 (by decide)).trans h8,
    (e 12 (by decide)).trans h12⟩

/-- After `k` blocks from `s`. -/
structure EInv (s : State) (up : Bool) (k : Nat) (u : State) : Prop where
  le : k ≤ (arg s 2).toNat
  esp : u.gpr .esp = s.gpr .esp
  ebp : u.gpr .ebp = arg s 3
  ptr : u.mem.readW (slot (arg s 3) 32) 32 = arg s 1 + BitVec.ofNat 32 (8 * k)
  cnt : u.mem.readW (slot (arg s 3) 36) 32 = BitVec.ofNat 32 ((arg s 2).toNat - k)
  saved : Saved u.mem (arg s 3) s
  done : ∀ b < k, blockAt u.mem (wAt ((arg s 1).setWidth 64) b) =
    blockOut (scheduleAt s.mem ((arg s 0).setWidth 64)) up (blockAt s.mem (wAt ((arg s 1).setWidth 64) b))
  rest : ∀ b, k ≤ b → b < (arg s 2).toNat →
    blockAt u.mem (wAt ((arg s 1).setWidth 64) b) = blockAt s.mem (wAt ((arg s 1).setWidth 64) b)
  frame : Frame [dataR s, scrR s] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem contains_pre (a : Addr) {n k : Nat} (h : n ≤ k) : Region.Contains ⟨a, k⟩ a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem mem_two {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem ecb_step {s : State} (h : EcbPre s) (up : Bool) {k : Nat} (hk : k < (arg s 2).toNat) {u : State}
    (I : EInv s up k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher 4 up) (.block storeBlock))) u fun u' =>
      EInv s up (k + 1) u' ∧ u'.zf = some (BitVec.ofNat 32 ((arg s 2).toNat - (k + 1)) == 0) := by
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, retD, retB, fK, fD, fB, fsp⟩ := h
  let S := arg s 0
  let D := arg s 1
  let B := arg s 3
  have eD : D.toNat = (arg s 1).toNat := rfl
  have eB : B.toNat = (arg s 3).toNat := rfl
  obtain bfit : B.toNat + 40 ≤ 2 ^ 32 := by omega_arith
  obtain hrw : u.rd ++ u.wr = [schR s, argR s, dataR s, scrR s] := by rw [I.rd, I.wr, hrd, hwr]; rfl
  obtain dR : dataR s ∈ u.wr := by rw [I.wr, hwr]; exact List.mem_cons_self
  obtain bR : scrR s ∈ u.wr := by rw [I.wr, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  let Pa := wAt (D.setWidth 64) k
  obtain eP : addr (D + BitVec.ofNat 32 (8 * k)) 0 = Pa := by
    rw [addr_of_fit (by omega_arith), BitVec.add_zero, ← addr, addr_of_fit (by omega_arith)]
  obtain e4 : addr (D + BitVec.ofNat 32 (8 * k)) 4 = Pa + BitVec.ofNat 64 4 := by
    unfold addr
    rw [ofs_add, ← addr, addr_of_fit (by omega_arith), Offset.add_add]
  obtain wK : InRegions u.wr Pa 8 := ⟨_, dR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain wS : ∀ d, d + 4 ≤ 40 → InRegions u.wr (slot B d) 4 := fun d hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain subK : Region.Sub ⟨Pa, 8⟩ (dataR s) := Offset.sub_base _ (by omega_arith)
  obtain subW : Region.Sub ⟨slot B 16, 24⟩ (scrR s) := Offset.sub_base _ (by omega_arith)
  obtain djK : Region.Disjoint ⟨slot B 16, 24⟩ ⟨Pa, 8⟩ := ((db.sub_left subK).sub_right subW).symm
  obtain sep16 : ∀ d, 16 ≤ d → d + 4 ≤ 40 → ∀ o, o ≤ 4 →
      Mem.Sep (slot B d) (32 / 8) (Pa + BitVec.ofNat 64 o) (32 / 8) := fun d h1 h2 o ho =>
    djK.sep (Offset.contains _ h1 (by omega_arith) (by omega_arith)) (Offset.contains_base _ (by omega_arith) (by omega_arith))
  -- the block in
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ebx] (loadBlock_run u (B := B) I.ebp bfit (wS 16 (by decide)) (wS 20 (by decide))
    (region_in (wS 32 (by decide))) I.ptr eP e4 (region_in (inRegions_pre wK (by decide)))
    (region_in (inRegions_off (o := 4) (n := 4) wK (by decide)))
    (sep_symm (sep16 16 (by decide) (by decide) 4 (by decide)))) (by decide))
    fun u₁ ⟨lm, lk⟩ => ?_
  obtain F1 : Frame (cRegion B) u.mem u₁.mem := by
    rw [lm]; exact frame_slot (frame_slot (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  -- what stays: the arguments, the schedule, the data
  obtain argOk : ∀ {m : Mem}, Frame [dataR s, scrR s] s.mem m → m.readW (argAddr s 0) 32 = S := fun hf =>
    hf.readW (contains_pre _ (by decide)) (fun r hr => (mem_two hr).elim (· ▸ ad) (· ▸ ab)) (by decide)
  obtain schOk : ∀ {m : Mem}, Frame [dataR s, scrR s] s.mem m →
      scheduleAt m (S.setWidth 64) = scheduleAt s.mem (S.setWidth 64) := fun hf =>
    scheduleAt_eq_of_frame _ hf fun r hr => (mem_two hr).elim (· ▸ kd) (· ▸ kb)
  obtain wide : ∀ {m m' : Mem}, Frame (cRegion B) m m' → Frame [dataR s, scrR s] m m' := fun hf =>
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩
  obtain hF1 : Frame [dataR s, scrR s] s.mem u₁.mem := I.frame.trans (wide F1)
  -- the cipher
  obtain CE : CipherEnv 4 S B u₁ := by
    obtain e1 : u₁.gpr .esp = s.gpr .esp := (lk.gpr (by decide)).trans I.esp
    refine ⟨(lk.gpr (by decide)).trans I.ebp, bfit, ?_, ?_, ?_, fK, fun o ho => ?_, ?_, ?_⟩
    · rw [lk.2.2]; exact inRegions_pre (N := 256) ⟨_, bR, Region.contains_self _ _⟩ (by decide)
    · rw [keep_reads lk, hrw, e1]
      exact ⟨argR s, List.mem_cons_of_mem _ List.mem_cons_self, contains_pre _ (by decide)⟩
    · rw [e1]; exact argOk hF1
    · rw [keep_reads lk, hrw]
      exact ⟨schR s, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · exact (kb.symm.sub_left (Region.sub_prefix (by decide)))
    · rw [e1]; exact (ab.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c12, ck, cf⟩ => ?_
  -- the block out
  obtain k₂ : Keep lookRegs u u₂ := (lk.trans ck).mono (by decide)
  obtain F2 : Frame (cRegion B) u.mem u₂.mem := F1.trans cf
  obtain past : ∀ d, 32 ≤ d → d + 4 ≤ 40 → u₂.mem.readW (slot B d) 32 = u.mem.readW (slot B d) 32 :=
    fun d h1 h2 => F2.readW (r := ⟨slot B d, 4⟩) (contains_pre _ (by decide)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint (B.setWidth 64) (d := d) (n := 4) (e := 16) (k := 16) (by omega_arith) (by omega_arith)
        (by omega_arith)) (by decide)
  obtain w₂ : ∀ d, d + 4 ≤ 40 → InRegions u₂.wr (slot B d) 4 := fun d hd => by rw [k₂.2.2]; exact wS d hd
  refine WP.mono (WP.keep [.eax, .ebx, .edx] (storeBlock_run u₂ (C := BitVec.ofNat 32 ((arg s 2).toNat - k))
    ((k₂.gpr (by decide)).trans I.ebp) bfit (region_in (w₂ 16 (by decide))) (region_in (w₂ 20 (by decide)))
    (w₂ 32 (by decide)) (w₂ 36 (by decide)) (by rw [past 32 (by decide) (by decide)]; exact I.ptr)
    (by rw [past 36 (by decide) (by decide)]; exact I.cnt) eP e4 (by rw [k₂.2.2]; exact inRegions_pre wK (by decide))
    (by rw [k₂.2.2]; exact inRegions_off (o := 4) (n := 4) wK (by decide))
    (sep16 20 (by decide) (by decide) 0 (by decide) |> fun h => by rwa [BitVec.add_zero] at h)) (by
      decide))
    fun u₃ ⟨⟨sm, sz⟩, sk⟩ => ?_
  obtain dj : Region.Disjoint ⟨slot B 32, 8⟩ ⟨Pa, 8⟩ := djK.sub_left (Offset.sub _ (by decide) (by decide))
  obtain ⟨M32, M36, MF, MB⟩ := stored_facts u₂.mem B Pa (u₂.mem.readW (slot B 16) 32)
    (u₂.mem.readW (slot B 20) 32) (D + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 8)
    (BitVec.ofNat 32 ((arg s 2).toNat - k) - BitVec.ofNat 32 1) dj
  rw [← sm] at M32 M36 MF MB
  obtain hcnt : BitVec.ofNat 32 ((arg s 2).toNat - k) - BitVec.ofNat 32 1 =
      BitVec.ofNat 32 ((arg s 2).toNat - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  -- the step's writes: the block and the working space's bytes 16–39
  obtain FS : Frame [⟨Pa, 8⟩, ⟨slot B 16, 24⟩] u.mem u₃.mem := by
    refine (F2.sub fun r hr => ?_).trans (MF.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
    · rcases mem_two hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  obtain dOther : ∀ b, b < (arg s 2).toNat → b ≠ k → ∀ r ∈ [(⟨Pa, 8⟩ : Region), ⟨slot B 16, 24⟩],
      (⟨wAt (D.setWidth 64) b, 8⟩ : Region).Disjoint r := fun b hb hne r hr => by
    rcases mem_two hr with rfl | rfl
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (db.sub_left (Offset.sub_base _ (by omega_arith))).sub_right subW
  obtain other : ∀ b, b < (arg s 2).toNat → b ≠ k →
      blockAt u₃.mem (wAt (D.setWidth 64) b) = blockAt u.mem (wAt (D.setWidth 64) b) :=
    fun b hb hne => blockAt_frame FS (dOther b hb hne)
  obtain k₃ : Keep [.eax, .ebx, .ecx, .edx, .esi, .edi] u u₃ := (k₂.trans sk).mono (by decide)
  refine ⟨⟨by omega_arith, (k₃.gpr (by decide)).trans I.esp, (k₃.gpr (by decide)).trans I.ebp,
    by rw [M32, ofs_add]; congr 2, by rw [M36, hcnt], ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩,
    by rw [sz, hcnt]⟩
  · refine I.saved.frame FS fun r hr => ?_
    rcases mem_two hr with rfl | rfl
    · exact (db.symm.sub_left (Region.sub_prefix (by decide))).sub_right subK
    · exact Offset.base_disjoint _ (by decide) (by omega_arith)
  · by_cases hbk : b = k
    · subst hbk
      obtain e16 : u₁.mem.readW (slot B 16) 32 = decodeWord (blockAt u.mem Pa) 0 := by
        rw [lm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
          Mem.readW_writeW_self32]
      obtain e20 : u₁.mem.readW (slot B 20) 32 = decodeWord (blockAt u.mem Pa) 4 := by
        rw [lm, Mem.readW_writeW_self32]
      rw [e16, e20, schOk hF1] at c12
      rw [MB, blockOut_eq, ← I.rest b (by omega_arith) hk, ← c12]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · refine I.frame.trans (FS.sub fun r hr => ?_)
    rcases mem_two hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subW⟩
  · rw [k₃.2.1, I.rd]
  · rw [k₃.2.2, I.wr]

/-- The memory once `save` has stored `b`, `si`, `di` and `bp` at `B`. -/
def savedMem (m : Mem) (B : BitVec 32) (b si di bp : BitVec 32) : Mem :=
  (((m.writeW (slot B 0) b).writeW (slot B 4) si).writeW (slot B 8) di).writeW (slot B 12) bp

theorem savedMem_frame (m : Mem) (B : BitVec 32) (b si di bp : BitVec 32) :
    Frame [⟨B.setWidth 64, 16⟩] m (savedMem m B b si di bp) := by
  unfold savedMem
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem saved_savedMem (m : Mem) (B : BitVec 32) (s₀ : State) :
    Saved (savedMem m B (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)) B s₀ := by
  unfold savedMem Saved
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (slot_sep B (d := 0) (e := 12) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (d := 0) (e := 8) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (d := 0) (e := 4) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (slot_sep B (d := 4) (e := 12) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (d := 4) (e := 8) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (slot_sep B (d := 8) (e := 12) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem ecb_start {s : State} (h : EcbPre s) :
    WP isa (.block (save ++ ([.mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp ptrOff) .ecx,
        .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp cntOff) .ecx, .alu .test .ecx (.reg .ecx)] : List Instr)))
      s fun u =>
      u.mem = ((savedMem s.mem (arg s 3) (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp)).writeW
        (slot (arg s 3) 32) (arg s 1)).writeW (slot (arg s 3) 36) (arg s 2) ∧
      u.gpr .ebp = arg s 3 ∧ u.zf = some (arg s 2 &&& arg s 2 == 0) := by
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, retD, retB, fK, fD, fB, fsp⟩ := h
  obtain bfit : (arg s 3).toNat + 40 ≤ 2 ^ 32 := by omega_arith
  obtain bR : scrR s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain wS : ∀ d, d + 4 ≤ 40 → InRegions s.wr (slot (arg s 3) d) 4 := fun d hd =>
    ⟨_, bR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain rA : ∀ i, i < 4 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [hrd]
    refine ⟨argR s, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨addr (s.gpr .esp) 4, 16⟩ (addr (s.gpr .esp) (4 + 4 * i)) 4
    rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith), ← Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain argF : ∀ {m : Mem}, Frame [scrR s] s.mem m → ∀ i, i < 4 →
      m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := fun hf i hi => by
    refine hf.readW (r := argR s) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ab) (by decide)
    show Region.Contains ⟨addr (s.gpr .esp) 4, 16⟩ (addr (s.gpr .esp) (4 + 4 * i)) 4
    rw [addr_of_fit (by omega_arith), addr_of_fit (by omega_arith), ← Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have a3 : s.mem.readW (addr (s.gpr .esp) 16) 32 = arg s 3 := rfl
  obtain r16 := rA 3 (by decide)
  obtain r8 := rA 1 (by decide)
  obtain r12 := rA 2 (by decide)
  obtain fM := fun bx si di bp => (savedMem_frame s.mem (arg s 3) bx si di bp).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  obtain m8 := fun bx si di bp => argF (fM bx si di bp) 1 (by decide)
  obtain m12 := fun bx si di bp (v : BitVec 32) => argF (m := (savedMem s.mem (arg s 3) bx si di bp).writeW (slot (arg s 3) 32) v)
    ((fM bx si di bp).writeW (List.mem_singleton_self _) _
      (Offset.contains_base (d := 32) (n := 4) (k := 256) _ (by decide) (by decide))) 2
    (by decide)
  simp only [savedMem] at m8 m12
  simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at r8 r12 r16 m8 m12
  unfold save
  brun [addr_slot bfit, a3, r16, r8, r12, wS 0 (by decide), wS 4 (by decide), wS 8 (by decide),
    wS 12 (by decide), wS 32 (by decide), wS 36 (by decide), m8, m12, savedMem]

/-- Restoring our caller's registers from the working space at `ebp`. -/
theorem restore_run (u s₀ : State) {B : BitVec 32} (hb : u.gpr .ebp = B) (bfit : B.toNat + 40 ≤ 2 ^ 32)
    (hr : ∀ d, d + 4 ≤ 16 → InRegions (u.rd ++ u.wr) (slot B d) 4) (hs : Saved u.mem B s₀) :
    WP isa (.block restore) u fun t =>
      t.gpr .ebx = s₀.gpr .ebx ∧ t.gpr .esi = s₀.gpr .esi ∧ t.gpr .edi = s₀.gpr .edi ∧
        t.gpr .ebp = s₀.gpr .ebp ∧ t.mem = u.mem := by
  obtain ⟨h0, h4, h8, h12⟩ := hs
  unfold restore
  brun [hb, addr_slot bfit, hr 0 (by decide), hr 4 (by decide), hr 8 (by decide), hr 12 (by decide),
    h0, h4, h8, h12]

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (if up then .encrypt else .decrypt) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- What ECB guarantees. -/
def EcbPost (s : State) (up : Bool) (t : State) : Prop :=
  abiPreserved s t ∧
    blocksAt t.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Blowfish.ecb (scheduleAt s.mem ((arg s 0).setWidth 64)) (if up then .encrypt else .decrypt)
        (blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)

theorem ecb_correct {s : State} (h : EcbPre s) (up : Bool) :
    WP isa (Impl.Blowfish.X86.ecb up) s (EcbPost s up) := by
  have H := h
  obtain ⟨hrd, hwr, kd, kb, db, ad, ab, retD, retB, fK, fD, fB, fsp⟩ := H
  let B := arg s 3
  have eB : B.toNat = (arg s 3).toNat := rfl
  obtain bfit : B.toNat + 40 ≤ 2 ^ 32 := by omega_arith
  unfold Impl.Blowfish.X86.ecb
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ecx, .ebp] (ecb_start h) (by decide))
    fun u₀ ⟨⟨um, ubp, uz⟩, uk⟩ => ?_
  obtain F0 : Frame [scrR s] s.mem u₀.mem := by
    rw [um]
    refine ((savedMem_frame s.mem B _ _ _ _).sub fun r hr => ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 32) (n := 4) (by decide) (by decide)) |>.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 36) (n := 4) (by decide) (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  obtain I0 : EInv s up 0 u₀ := by
    refine ⟨Nat.zero_le _, uk.gpr (by decide), ubp, ?_, ?_, ?_, fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b _ hb => blockAt_frame F0 fun r hr => ?_, F0.mono fun r hr => ?_, uk.2.1, uk.2.2⟩
    · rw [um, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self32, Nat.mul_zero]; simp
    · rw [um, Mem.readW_writeW_self32, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · refine (saved_savedMem s.mem B s).frame (rs := [⟨slot B 32, 8⟩]) ?_ fun r hr => ?_
      · rw [um]
        exact ((Frame.refl _ _).writeW List.mem_cons_self _
          (Offset.contains (e := 32) (k := 8) (d := 32) (n := 4) _ (by decide) (by decide) (by decide))).writeW
          List.mem_cons_self _ (Offset.contains (e := 32) (k := 8) (d := 36) (n := 4) _ (by decide) (by decide)
            (by decide))
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      exact db.sub_left (Offset.sub_base _ (by omega_arith))
    · simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the end
  obtain fin : ∀ u, EInv s up (arg s 2).toNat u → WP isa (.block restore) u (EcbPost s up) := fun u I => by
    obtain hr : ∀ d, d + 4 ≤ 16 → InRegions (u.rd ++ u.wr) (slot B d) 4 := fun d hd => by
      rw [I.rd, I.wr, hrd, hwr]
      exact ⟨scrR s, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    refine WP.mono (WP.keep [.ebx, .esi, .edi, .ebp] (restore_run u s I.ebp bfit hr I.saved) (by
        decide))
      fun t ⟨⟨tb, ts, td, tp, tm⟩, tk⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ecb_blocks _ _ _ _ _ _ fun b hb => by
        rw [tm]; exact I.done b hb⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [tb, ts, td, tp, (tk.gpr (by decide)).trans I.esp]
    · rw [tm]
      refine I.frame.readW (r := retR s) (contains_pre _ (by decide)) (fun r hr => ?_) (by decide)
      rcases mem_two hr with rfl | rfl
      exacts [retD, retB]
  apply WP.seq
  rw [BitVec.and_self] at uz
  refine WP.ite (arg s 2 == 0) (by rw [eval_e, uz]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (arg s 2).toNat = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz); simpa using this
    exact WP.block_nil (fin u₀ (by rw [hn]; exact I0))
  · have hn : 0 < (arg s 2).toNat := by
      obtain h0 : arg s 2 ≠ 0 := by intro e; rw [e] at hz; simp at hz
      have : (arg s 2).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
      omega_arith
    refine WP.mono (WP.loop (M := isa) (Q := EInv s up (arg s 2).toNat)
      (fun (m : Nat) (u : State) => ∃ k, k < (arg s 2).toNat ∧ m = (arg s 2).toNat - k ∧ EInv s up k u)
      ?_ _ u₀ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step h up hk I) fun u' ⟨I', zu⟩ => ?_
    rw [eval_ne, zu]
    by_cases e : k + 1 = (arg s 2).toNat
    · left
      exact ⟨by rw [e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      obtain nz : BitVec.ofNat 32 ((arg s 2).toNat - (k + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega_arith
      exact ⟨by rw [beq_eq_false_iff_ne.mpr nz]; rfl, _, by omega_arith, k + 1, by omega_arith, rfl, I'⟩

end VG.Proof.Blowfish.X86
