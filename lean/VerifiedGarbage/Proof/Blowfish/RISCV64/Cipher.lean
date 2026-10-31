module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Lookup
public import VerifiedGarbage.Proof.Blowfish.Feistel
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Blowfish on RISCV64: F and the block function

`f_run`: F of xL's low word into `a5`'s, one S-box at a time (`fAcc`).
`cipher_run`: `cipher up` takes the halves in the low words of `a3` and
`a4` to their encryption (`up`) or decryption under the schedule at `a7`,
changing only `a3`–`a6` and the lookup's temporaries. The structure of
PPC64LE's (`Proof/Blowfish/PPC64LE/Cipher.lean`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## F -/

/-- The registers F writes. -/
def fRegs : List Reg := .a5 :: lookRegs

theorem combine_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [combine j]) u fun t =>
      lo (t.gpr .a5) = (if j = 0 then lo (u.gpr .t2) else if j = 2 then lo (u.gpr .a5) ^^^ lo (u.gpr .t2)
        else lo (u.gpr .a5) + lo (u.gpr .t2)) ∧ t.mem = u.mem := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine] <;> simp only [lo_xor, lo_add, BitVec.or_self]

/-- What a run of `Keep (r :: rs)` that leaves `r` as it was keeps. -/
theorem keep_restore {r : Reg} {rs : List Reg} {s t : State} (h : Keep (r :: rs) s t)
    (hr : t.gpr r = s.gpr r) : Keep rs s t :=
  ⟨fun r' h' => by
    by_cases e : r' = r
    · rw [e]; exact hr
    · exact h.1 r' (by simp only [List.mem_cons, not_or]; exact ⟨e, h'⟩), h.2⟩

/-- The registers F writes, with the schedule pointer, which it moves and
restores. -/
def fRegs7 : List Reg := .a7 :: fRegs

/-- S-box `j`'s lookup, then its accumulation, from `fAcc … (j - 1)` (or
anything, for `j = 0`) in `a5`, with `sch` at S-box `j`. -/
theorem step_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs7 s₀ u)
    (hm : u.mem = s₀.mem) (h7 : u.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j))
    (hp : 0 < j → lo (u.gpr .a5) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7))
      (lo (s₀.gpr .a3)) (j - 1)) {Q : State → Prop}
    (hQ : ∀ t, lo (t.gpr .a5) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7)) (lo (s₀.gpr .a3)) j →
      Keep fRegs7 s₀ t → t.mem = s₀.mem → t.gpr .a7 = u.gpr .a7 → Q t) :
    WP isa (.seq (lookup j) (.block [combine j])) u Q := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [k.2.1, k.2.2]
  have Eu : SchAt u (s₀.gpr .a7) := ⟨fun o h1 h2 => by rw [hrd]; exact E.rd8 o h1 h2, E.al8⟩
  apply WP.seq
  refine WP.mono (lookup_run Eu hj h7) fun v ⟨v10, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.a5] (combine_run v hj) (by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun t ⟨⟨t7, tm⟩, tk⟩ => hQ t ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
      (by rw [tk.gpr (by decide), vk.gpr (by decide)])
  have e4 : u.gpr .a3 = s₀.gpr .a3 := k.gpr (by decide)
  rw [t7, v10, hm, e4, vk.gpr (by decide)]
  exact fAcc_step _ _ hj _ hp

theorem nextBox_run (u : State) :
    WP isa (.block [nextBox]) u fun t => t.gpr .a7 = u.gpr .a7 + BitVec.ofNat 64 1024 ∧ t.mem = u.mem := by
  brun [nextBox]

/-- `nextBox` after the lookup of S-box `j < 3`, and what it keeps. -/
theorem next_run {s₀ : State} {j : Nat} {u : State} (k : Keep fRegs7 s₀ u)
    (h7 : u.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j)) :
    WP isa (.block [nextBox]) u fun t => Keep fRegs7 s₀ t ∧ t.mem = u.mem ∧
      t.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * (j + 1)) ∧ t.gpr .a5 = u.gpr .a5 := by
  refine WP.mono (WP.keep [.a7] (nextBox_run u) (by rfl) rfl) fun t ⟨⟨t7, tm⟩, tk⟩ =>
    ⟨(k.trans tk).mono (by decide), tm, ?_, tk.gpr (by decide)⟩
  rw [t7, h7, Offset.add_add]
  congr 2

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.RISCV64.f s fun t =>
      lo (t.gpr .a5) = Spec.Blowfish.f (scheduleAt s.mem (s.gpr .a7)) (lo (s.gpr .a3)) ∧
        Keep fRegs s t ∧ t.mem = s.mem := by
  unfold Impl.Blowfish.RISCV64.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl (by simp) (fun h => absurd h (by decide))
    fun t0 h0 k0 m0 e0 => ?_
  apply WP.seq
  refine WP.mono (next_run (j := 0) k0 (by rw [e0]; simp)) fun u0 ⟨k0', m0', e0', a0⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0' (m0'.trans m0) e0' (fun _ => by rw [a0]; exact h0)
    fun t1 h1 k1 m1 e1 => ?_
  apply WP.seq
  refine WP.mono (next_run (j := 1) k1 (by rw [e1, e0'])) fun u1 ⟨k1', m1', e1', a1⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1' (m1'.trans m1) e1' (fun _ => by rw [a1]; exact h1)
    fun t2 h2 k2 m2 e2 => ?_
  apply WP.seq
  refine WP.mono (next_run (j := 2) k2 (by rw [e2, e1'])) fun u2 ⟨k2', m2', e2', a2⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 3) (by decide) k2' (m2'.trans m2) e2' (fun _ => by rw [a2]; exact h2)
    fun t3 h3 k3 m3 e3 => ?_
  have back : WP isa (.block [.addi sch sch (-2048), .addi sch sch (-1024)]) t3 fun t =>
      t.gpr .a7 = t3.gpr .a7 - BitVec.ofNat 64 2048 - BitVec.ofNat 64 1024 ∧ t.mem = t3.mem := by
    brun
  refine WP.mono (WP.keep [.a7] back (by rfl) rfl) fun t ⟨⟨t7, tm⟩, tk⟩ => ?_
  have e7 : t.gpr .a7 = s.gpr .a7 := by
    rw [t7, e3, e2', BitVec.sub_sub, BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  refine ⟨?_, keep_restore ((k3.trans tk).mono (by decide)) e7, tm.trans m3⟩
  rw [tk.gpr (by decide), h3, fAcc_three]

/-! ## Rounds -/

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem ofs_sub (S : BitVec 64) {a b : Nat} (h : b ≤ a) :
    S + BitVec.ofNat 64 a - BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The address of the P-array entry of round `i`. -/
theorem addr_P (S : BitVec 64) (up : Bool) {i : Nat} (hi : i < 16) :
    S + BitVec.ofNat 64 (pBase up i) + BitVec.ofNat 64 (pAt up) = S + BitVec.ofNat 64 (4096 + 4 * ord up i) :=
  Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord] <;> omega)

/-- After `i` rounds from `s₀`. -/
structure CInv (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  p : u.gpr .a6 = s₀.gpr .a7 + BitVec.ofNat 64 (pBase up i)
  halves : (lo (u.gpr .a3), lo (u.gpr .a4)) =
    iter (scheduleAt s₀.mem (s₀.gpr .a7)) (ord up) i (lo (s₀.gpr .a3), lo (s₀.gpr .a4))
  keep : Keep cRegs s₀ u
  mem : u.mem = s₀.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : u.gpr .a6 + BitVec.ofNat 64 (pAt up) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hal : a.toNat % 4 = 0) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp]) u fun t =>
      lo (t.gpr .a3) = lo (u.gpr .a3) ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 2048 := by cases up <;> decide
  rw [← hp] at hr hP hal
  brun [ho, hr, hP, hal]
  simp only [lo_xor, lo_ext]

/-- The round's end test: `pPtr - sch` less the end offset, in three
immediates. -/
theorem sub_end (S : Addr) (a : Nat) {e : Nat} (he : 4094 ≤ e) :
    S + BitVec.ofNat 64 a - S - BitVec.ofNat 64 2047 - BitVec.ofNat 64 2047 - BitVec.ofNat 64 (e - 4094) =
      BitVec.ofNat 64 a - BitVec.ofNat 64 e := by
  rw [Offset.add_sub_cancel_left, BitVec.sub_sub, BitVec.sub_sub, BitVec.ofNat_add_ofNat,
    BitVec.ofNat_add_ofNat, show 2047 + (2047 + (e - 4094)) = e by omega]

theorem round_tail (u : State) (up : Bool) (S : BitVec 64) {i : Nat} (hi : i < 16)
    (h3 : u.gpr .a7 = S) (h8 : u.gpr .a6 = S + BitVec.ofNat 64 (pBase up i)) :
    WP isa (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR,
        .logic .or xR tmp tmp, .addi pPtr pPtr (if up then 4 else -4),
        .sub tmp pPtr sch, .addi tmp tmp (-2047), .addi tmp tmp (-2047),
        .addi tmp tmp (-(pEnd up - 4094 : Nat))]) u fun t =>
      lo (t.gpr .a3) = lo (u.gpr .a4) ^^^ lo (u.gpr .a5) ∧ lo (t.gpr .a4) = lo (u.gpr .a3) ∧
        t.gpr .a6 = S + BitVec.ofNat 64 (pBase up (i + 1)) ∧
        t.gpr .t4 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) ∧
        t.mem = u.mem := by
  have hend : pEnd up = pBase up 16 := by cases up <;> rfl
  have e4 : 4094 ≤ pEnd up := by cases up <;> decide
  cases up
  · have e : S + BitVec.ofNat 64 (4160 - 4 * i) - 4#64 = S + BitVec.ofNat 64 (4160 - 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofs_sub S (by omega)]; congr 2
    brun [h3, h8, show pEnd false - 4094 ≤ 2048 by decide]
    simp only [pBase, Bool.false_eq_true, ite_false, lo_xor, BitVec.or_self, e]
    refine ⟨trivial, trivial, trivial, ?_⟩
    rw [sub_end S _ e4, hend]
    simp only [pBase, Bool.false_eq_true, ite_false]
  · have e : S + BitVec.ofNat 64 (4096 + 4 * i) + 4#64 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    brun [h3, h8, show pEnd true - 4094 ≤ 2048 by decide]
    simp only [pBase, ite_true, lo_xor, BitVec.or_self, e]
    refine ⟨trivial, trivial, trivial, ?_⟩
    rw [sub_end S _ e4, hend]
    simp only [pBase, ite_true]

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2]

theorem round_step {s₀ : State} (E : LookEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧
      u'.gpr .t4 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) := by
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega
  let K := scheduleAt s₀.mem (s₀.gpr .a7)
  have u3 : u.gpr .a7 = s₀.gpr .a7 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.a3, .t4] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P _ up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega) (by omega))
    (al_add E.al (by omega) (by omega))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide) rfl) fun v ⟨⟨v4, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := (I.keep.trans vk).mono (by decide)
  have Ev : LookEnv v := E.keep kv (by decide)
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w7, wk, wm⟩ => ?_
  have w3 : w.gpr .a7 = s₀.gpr .a7 := by rw [wk.gpr (by decide), vk.gpr (by decide), u3]
  have w8 : w.gpr .a6 = s₀.gpr .a7 + BitVec.ofNat 64 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.a3, .a4, .a6, .t4] (round_tail w up _ hi w3 w8) (by
    cases up <;> decide) rfl) fun x ⟨⟨x4, x5, x8, x12, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (v.gpr .a7) = K := by rw [vm, I.mem, vk.gpr (by decide), u3]
  refine ⟨⟨by omega, x8, ?_, ((kv.trans wk).trans xk).mono (by decide), by rw [xm, wm, vm, I.mem]⟩, x12⟩
  have w4 : w.gpr .a3 = v.gpr .a3 := wk.gpr (by decide)
  have w5 : w.gpr .a4 = u.gpr .a4 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
  rw [x4, x5, w7, hK, w4, w5, v4, iter_succ, ← I.halves]
  simp only [roundStep]
  rw [BitVec.xor_comm (lo (u.gpr .a4))]

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block [.addi pPtr sch 2047, .addi pPtr pPtr 2047,
      .addi pPtr pPtr ((if up then pOff else pOff + 64) - 4094 : Nat)]) s fun t =>
      t.gpr .a6 = s.gpr .a7 + BitVec.ofNat 64 (pBase up 0) ∧ t.mem = s.mem := by
  cases up <;> brun [pOff, pBase] <;> rw [Offset.add_add, Offset.add_add]

theorem rounds_run {s : State} (E : LookEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) (.nonzero tmp)) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [tmp, Steps.eval_nonzero, hz, ofNat_sub_bne (by cases up <;> simp [pBase] <;> omega)
    (by cases up <;> simp [pBase])]
  have e : (pBase up (i + 1) = pBase up 16) ↔ i + 1 = 16 := by cases up <;> simp [pBase] <;> omega
  by_cases e' : i + 1 = 16
  · left
    exact ⟨by simp [e.mpr e'], e' ▸ J'⟩
  · right
    have hne : ¬ pBase up (i + 1) = pBase up 16 := fun h => e' (e.mp h)
    exact ⟨by simp [hne], n - 1, by omega, i + 1, by omega, by omega, J'⟩

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : u.gpr .a6 + BitVec.ofNat 64 (pAt up) = a)
    (hb : u.gpr .a6 + BitVec.ofNat 64 (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (hla : a.toNat % 4 = 0) (hlb : b.toNat % 4 = 0)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor tmp xL tmp,
        .load .w xL pPtr (4 - pAt up), .logic .xor xL xL xR, .logic .or xR tmp tmp]) u fun t =>
      lo (t.gpr .a3) = P₁₇ ^^^ lo (u.gpr .a4) ∧ lo (t.gpr .a4) = lo (u.gpr .a3) ^^^ P₁₆ ∧
        t.mem = u.mem := by
  have ho : pAt up < 2048 := by cases up <;> decide
  have ho' : 4 - pAt up < 2048 := by cases up <;> decide
  rw [← ha] at hra h16 hla
  rw [← hb] at hrb h17 hlb
  brun [ho, ho', hra, hrb, h16, h17, hla, hlb]
  simp only [lo_xor, lo_ext, BitVec.or_self, and_self]

/-- The block function. -/
theorem cipher_run {s : State} (E : LookEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (lo (t.gpr .a3), lo (t.gpr .a4)) =
        feistel (scheduleAt s.mem (s.gpr .a7)) (ord up) (lo (s.gpr .a3)) (lo (s.gpr .a4)) ∧
      Keep cRegs s t ∧ t.mem = s.mem := by
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.a6] (cipher_start s up) (by cases up <;> decide) rfl)
    fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u8, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (s.gpr .a7)
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.a3, .a4, .t4] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := s.gpr .a7 + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := s.gpr .a7 + BitVec.ofNat 64 (4096 + 4 * ord up 17))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [hrd]; exact E.rd _ (by omega) r16) (by rw [hrd]; exact E.rd _ (by omega) r17)
    (al_add E.al (by omega) (by omega)) (al_add E.al (by omega) (by omega))
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide) rfl)
    fun t ⟨⟨t4, t5, tm⟩, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans tk).mono (by decide), by rw [tm, V.mem]⟩
  rw [t4, t5, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.RISCV64
