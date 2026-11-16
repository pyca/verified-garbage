module

public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Rc4.Dword
import VerifiedGarbage.Proof.Blowfish.Schedule
public import VerifiedGarbage.Proof.Blowfish.Feistel

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
