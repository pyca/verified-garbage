module

public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Rc4.Dword

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
  have r := keep_reads h
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
  have h255 : (BitVec.ofNat 32 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  simp only [ite_true, ite_false, Nat.reduceLT, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, h255,
    Nat.reduceMul, Nat.reduceSub, hi, decide_true, Bool.true_and] <;>
  by_cases h8 : i < 8 <;> simp (disch := omega) [h8, BitVec.getLsbD_of_ge, Nat.add_comm]

theorem index_run (s : State) {j : Nat} (hj : j < 4) {x : BitVec 32}
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) xlOff) 4)
    (hx : s.mem.readW (addr (s.gpr .ebp) xlOff) 32 = x) :
    WP isa (.block (index j)) s fun t => t.gpr .esi = (quarter x j).setWidth 32 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
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
  have e : q &&& BitVec.ofNat 32 3 = BitVec.ofNat 32 L := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (3 % 2 ^ 32 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e' : ∀ d : BitVec 32, d = BitVec.ofNat 32 3 &&& d → q &&& d = BitVec.ofNat 32 L &&& d := by
    intro d hd
    conv => lhs; rw [hd]
    rw [← BitVec.and_assoc, e]
  rcases hc with rfl | rfl
  · exact e' _ (by decide)
  · exact e' _ (by decide)

theorem bitClr_lane (q : BitVec 32) {L : Nat} (hL : q.toNat % 4 = L) :
    bitClr q 1 = !decide (L % 2 = 1) ∧ bitClr q 2 = !decide (L / 2 = 1) := by
  have hl : L < 4 := by omega
  unfold bitClr
  rw [and_lane q hL (.inl rfl), and_lane q hL (.inr rfl)]
  rcases (by omega : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3) with rfl | rfl | rfl | rfl <;> decide

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
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  unfold row plane
  brun [hsi, hdi, hax, hbx, hs, hrs, r0, r1, r2, r3]
  simp only [row_mask, Nat.reduceMul, Nat.reduceSub]
theorem addr_row {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) {j b k : Nat} (hj : j < 4) (hb : b < 4)
    (hk : k < 64) :
    addr (S + BitVec.ofNat 32 (4 * k)) (planeOff j b) = S.setWidth 64 + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k) := by
  unfold addr
  rw [ofs_add, ← addr, addr_of_fit (by unfold planeOff; omega)]
  congr 2; unfold planeOff; omega

/-- The lane mask, the accumulator and the row pointer. -/
theorem start_run (s : State) {sch : Nat} {S : BitVec 32} (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) sch) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) sch) 32 = S) {L : Nat} (hL : (s.gpr .esi).toNat % 4 = L) :
    WP isa (.block (lookupStart sch)) s fun t =>
      t.gpr .eax = laneMask L ∧ t.gpr .edi = 0 ∧ t.gpr .ebx = S ∧ t.mem = s.mem := by
  have hl : L < 4 := by omega
  obtain ⟨b1, b2⟩ := bitClr_lane _ hL
  unfold lookupStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h0 : WP isa (.block [.mov .eax (imm 255)]) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 255 ∧ t.mem = s.mem := by brun
  refine WP.mono (WP.keep [.eax] h0 (by decide)) fun t₀ ⟨⟨t7, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (condRot_run t₀ .eax (c := 1) (a := 24) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide)) fun t₁ ⟨⟨u7, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (condRot_run t₁ .eax (c := 2) (a := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide)) fun t₂ ⟨⟨v7, vm⟩, vk⟩ => ?_
  have q1 : t₀.gpr .esi = s.gpr .esi := tk.gpr (by decide)
  have q2 : t₁.gpr .esi = s.gpr .esi := (uk.gpr (by decide)).trans q1
  have k2 : Keep [.eax, .ecx, .edx] s t₂ := ((tk.trans uk).trans vk).mono (by decide)
  have e7 : t₂.gpr .eax = laneMask L := by
    rw [v7, u7, q2, q1, t7, b1, b2, not_ite, not_ite]; exact laneMask_rot hl
  have em : t₂.mem = s.mem := by rw [vm, um, tm]
  have er : InRegions (t₂.rd ++ t₂.wr) (addr (t₂.gpr .esp) sch) 4 := by
    rw [keep_reads k2, k2.gpr (by decide)]; exact hr
  have ev : t₂.mem.readW (addr (t₂.gpr .esp) sch) 32 = S := by rw [em, k2.gpr (by decide)]; exact hv
  have ev' : s.mem.readW (addr (t₂.gpr .esp) sch) 32 = S := by rw [k2.gpr (by decide)]; exact hv
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
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := keep_reads I.keep
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (addr (S + BitVec.ofNat 32 (4 * k)) (planeOff j b)) 4 :=
    fun b hb => by rw [addr_row fit hj hb hk, hrd]; exact E.rd _ (by omega)
  have hsp : u.gpr .esp = s₀.gpr .esp := I.keep.gpr (by decide)
  refine WP.mono (WP.keep [.ebx, .ecx, .edx, .esi, .edi] (row_run u (S := S) I.q I.acc I.lane I.rp
    (by rw [I.mem, hsp]; exact E.schVal) (by rw [hrd, hsp]; exact E.schRd) hr) (by
      simp [writesOnly, row, plane, Code.allInstrs, Taint.clobbers, Taint.dst, VG.Proof.MlDsa.X86.Pack.allRegs]))
    fun u' ⟨⟨a5, a4, a10, az, am⟩, ak⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, Keep.trans_sub I.keep ak (by decide), am.trans I.mem⟩, ?_⟩
  · rw [a4, BitVec.sub_sub, ← BitVec.ofNat_add]; congr 2
  · dsimp only at a5
    have e : ∀ q lm : BitVec 32, q = idx.setWidth 32 - BitVec.ofNat 32 (4 * k) →
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
      ofNat_sub_beq' (by omega) (by decide)]
    congr 2; apply propext; omega

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
    exact ⟨by simp [e], n - 1, by omega, k + 1, by omega, by omega, J'⟩

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
  have hL : (t.gpr .esi).toNat % 4 = idx.toNat % 4 := by rw [t4, BitVec.toNat_setWidth]; simp [idx]
  have Et := E.keep tk tm (by decide) (by decide)
  refine WP.mono (WP.keep [.eax, .ebx, .ecx, .edx, .edi] (start_run t Et.schRd Et.schVal hL) (by
      simp [writesOnly, lookupStart, condRot, Code.allInstrs, Taint.clobbers, Taint.dst,
        VG.Proof.MlDsa.X86.Pack.allRegs]))
    fun u ⟨⟨u7, u5, u10, um⟩, uk⟩ => ?_
  have K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  have I0 : RowInv s S j idx 0 u := by
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
  have hL4 : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨b1, b2⟩ := bitClr_lane _ (sub256_mod idx)
  refine ⟨?_, ((V.keep.trans wk).trans yk).mono (by decide), by rw [ym, wm, V.mem]⟩
  rw [y5, w5, wk.gpr (by decide), V.q, b1, b2, not_ite, not_ite, acc_rot _ hL4, V.acc, scanAcc_all]
  exact hitWord_ror _ _ hj idx

end VG.Proof.Blowfish.X86
