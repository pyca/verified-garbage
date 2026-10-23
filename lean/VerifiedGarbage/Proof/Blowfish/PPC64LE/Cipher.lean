module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Blowfish.Feistel
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Blowfish on PPC64LE: F and the block function

`f_run`: F of xL's low word into `r7`'s, one S-box at a time (`fAcc`).
`cipher_run`: `cipher up` takes the halves in the low words of `r4` and
`r5` to their encryption (`up`) or decryption under the schedule at `r3`,
changing only `r4`, `r5`, `r7`–`r12`, `r14` and `r15`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## F -/

/-- The registers F writes. -/
def fRegs : List Reg := .r7 :: lookRegs

theorem combine_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [combine j]) u fun t =>
      lo (t.gpr .r7) = (if j = 0 then lo (u.gpr .r10) else if j = 2 then lo (u.gpr .r7) ^^^ lo (u.gpr .r10)
        else lo (u.gpr .r7) + lo (u.gpr .r10)) ∧ t.mem = u.mem := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine] <;> simp only [lo_xor, lo_add, BitVec.or_self]

/-- S-box `j`'s lookup, then its accumulation, from `fAcc … (j - 1)` (or
anything, for `j = 0`) in `r7`. -/
theorem step_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs s₀ u)
    (hm : u.mem = s₀.mem) (h7 : 0 < j → lo (u.gpr .r7) = fAcc (scheduleAt s₀.mem (s₀.gpr .r3))
      (lo (s₀.gpr .r4)) (j - 1)) {Q : State → Prop}
    (hQ : ∀ t, lo (t.gpr .r7) = fAcc (scheduleAt s₀.mem (s₀.gpr .r3)) (lo (s₀.gpr .r4)) j →
      Keep fRegs s₀ t → t.mem = s₀.mem → Q t) :
    WP isa (.seq (lookup j) (.block [combine j])) u Q := by
  have Eu : LookEnv u := E.keep k (by decide) (by decide)
  apply WP.seq
  refine WP.mono (lookup_run Eu hj) fun v ⟨v10, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.r7] (combine_run v hj) (by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun t ⟨⟨t7, tm⟩, tk⟩ => hQ t ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
  have e3 : u.gpr .r3 = s₀.gpr .r3 := k.gpr (by decide)
  have e4 : u.gpr .r4 = s₀.gpr .r4 := k.gpr (by decide)
  rw [t7, v10, hm, e3, e4, vk.gpr (by decide)]
  exact fAcc_step _ _ hj _ h7

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.PPC64LE.f s fun t =>
      lo (t.gpr .r7) = Spec.Blowfish.f (scheduleAt s.mem (s.gpr .r3)) (lo (s.gpr .r4)) ∧
        Keep fRegs s t ∧ t.mem = s.mem := by
  unfold Impl.Blowfish.PPC64LE.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl (fun h => absurd h (by decide))
    fun t0 h0 k0 m0 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0 m0 (fun _ => h0) fun t1 h1 k1 m1 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1 m1 (fun _ => h1) fun t2 h2 k2 m2 => ?_
  refine step_run E (j := 3) (by decide) k2 m2 (fun _ => h2) fun t3 h3 k3 m3 => ?_
  exact ⟨by rw [h3, fAcc_three], k3, m3⟩

/-! ## Rounds -/

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15]

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
  p : u.gpr .r8 = s₀.gpr .r3 + BitVec.ofNat 64 (pBase up i)
  halves : (lo (u.gpr .r4), lo (u.gpr .r5)) =
    iter (scheduleAt s₀.mem (s₀.gpr .r3)) (ord up) i (lo (s₀.gpr .r4), lo (s₀.gpr .r5))
  keep : Keep cRegs s₀ u
  mem : u.mem = s₀.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : u.gpr .r8 + BitVec.ofNat 64 (pAt up) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp]) u fun t =>
      lo (t.gpr .r4) = lo (u.gpr .r4) ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 2 ^ 15 := by cases up <;> decide
  rw [← hp] at hr hP
  brun [ho, hr, hP]
  simp only [lo_xor, lo_ext]

theorem round_tail (u : State) (up : Bool) (S : BitVec 64) {i : Nat} (hi : i < 16)
    (h3 : u.gpr .r3 = S) (h8 : u.gpr .r8 = S + BitVec.ofNat 64 (pBase up i)) :
    WP isa (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR,
        .logic .or xR tmp tmp, if up then .addi pPtr pPtr 4 else .subi pPtr pPtr 4,
        .sub tmp pPtr sch, .subi tmp tmp (if up then pOff + 64 else pOff)]) u fun t =>
      lo (t.gpr .r4) = lo (u.gpr .r5) ^^^ lo (u.gpr .r7) ∧ lo (t.gpr .r5) = lo (u.gpr .r4) ∧
        t.gpr .r8 = S + BitVec.ofNat 64 (pBase up (i + 1)) ∧
        t.gpr .r12 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) ∧
        t.mem = u.mem := by
  cases up
  · brun [h3, h8, pOff]
    simp only [pBase, Bool.false_eq_true, ite_false, lo_xor, BitVec.or_self]
    have e : S + BitVec.ofNat 64 (4160 - 4 * i) - 4#64 = S + BitVec.ofNat 64 (4160 - 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofs_sub S (by omega)]; congr 2
    refine ⟨trivial, trivial, e, ?_⟩
    rw [e, Offset.add_sub_cancel_left]
  · brun [h3, h8, pOff]
    simp only [pBase, ite_true, lo_xor, BitVec.or_self]
    have e : S + BitVec.ofNat 64 (4096 + 4 * i) + 4#64 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    refine ⟨trivial, trivial, e, ?_⟩
    rw [e, Offset.add_sub_cancel_left]

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2]

theorem round_step {s₀ : State} (E : LookEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧
      u'.gpr .r12 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) := by
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega
  let K := scheduleAt s₀.mem (s₀.gpr .r3)
  have u3 : u.gpr .r3 = s₀.gpr .r3 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r12] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P _ up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide) rfl) fun v ⟨⟨v4, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := (I.keep.trans vk).mono (by decide)
  have Ev : LookEnv v := E.keep kv (by decide) (by decide)
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w7, wk, wm⟩ => ?_
  have w3 : w.gpr .r3 = s₀.gpr .r3 := by rw [wk.gpr (by decide), vk.gpr (by decide), u3]
  have w8 : w.gpr .r8 = s₀.gpr .r3 + BitVec.ofNat 64 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.r4, .r5, .r8, .r12] (round_tail w up _ hi w3 w8) (by
    cases up <;> decide) rfl) fun x ⟨⟨x4, x5, x8, x12, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (v.gpr .r3) = K := by rw [vm, I.mem, vk.gpr (by decide), u3]
  refine ⟨⟨by omega, x8, ?_, ((kv.trans wk).trans xk).mono (by decide), by rw [xm, wm, vm, I.mem]⟩, x12⟩
  have w4 : w.gpr .r4 = v.gpr .r4 := wk.gpr (by decide)
  have w5 : w.gpr .r5 = u.gpr .r5 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
  rw [x4, x5, w7, hK, w4, w5, v4, iter_succ, ← I.halves]
  simp only [roundStep]
  rw [BitVec.xor_comm (lo (u.gpr .r5))]

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block [.addi pPtr sch (if up then pOff else pOff + 64)]) s fun t =>
      t.gpr .r8 = s.gpr .r3 + BitVec.ofNat 64 (pBase up 0) ∧ t.mem = s.mem := by
  cases up <;> brun [pOff, pBase]

theorem rounds_run {s : State} (E : LookEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) (.nonzero .d tmp)) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [tmp, eval_nonzero, hz, ofNat_sub_bne (by cases up <;> simp [pBase] <;> omega)
    (by cases up <;> simp [pBase])]
  have e : (pBase up (i + 1) = pBase up 16) ↔ i + 1 = 16 := by cases up <;> simp [pBase] <;> omega
  by_cases e' : i + 1 = 16
  · left
    exact ⟨by simp [e.mpr e'], e' ▸ J'⟩
  · right
    have hne : ¬ pBase up (i + 1) = pBase up 16 := fun h => e' (e.mp h)
    exact ⟨by simp [hne], n - 1, by omega, i + 1, by omega, by omega, J'⟩

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : u.gpr .r8 + BitVec.ofNat 64 (pAt up) = a)
    (hb : u.gpr .r8 + BitVec.ofNat 64 (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor tmp xL tmp,
        .load .w xL pPtr (4 - pAt up), .logic .xor xL xL xR, .logic .or xR tmp tmp]) u fun t =>
      lo (t.gpr .r4) = P₁₇ ^^^ lo (u.gpr .r5) ∧ lo (t.gpr .r5) = lo (u.gpr .r4) ^^^ P₁₆ ∧
        t.mem = u.mem := by
  have ho : pAt up < 2 ^ 15 := by cases up <;> decide
  have ho' : 4 - pAt up < 2 ^ 15 := by cases up <;> decide
  rw [← ha] at hra h16
  rw [← hb] at hrb h17
  brun [ho, ho', hra, hrb, h16, h17]
  simp only [lo_xor, lo_ext, BitVec.or_self, and_self]

/-- The block function. -/
theorem cipher_run {s : State} (E : LookEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (lo (t.gpr .r4), lo (t.gpr .r5)) =
        feistel (scheduleAt s.mem (s.gpr .r3)) (ord up) (lo (s.gpr .r4)) (lo (s.gpr .r5)) ∧
      Keep cRegs s t ∧ t.mem = s.mem := by
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.r8] (cipher_start s up) (by cases up <;> decide) rfl)
    fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u8, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (s.gpr .r3)
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.r4, .r5, .r12] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := s.gpr .r3 + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := s.gpr .r3 + BitVec.ofNat 64 (4096 + 4 * ord up 17))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [hrd]; exact E.rd _ r16) (by rw [hrd]; exact E.rd _ r17)
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide) rfl)
    fun t ⟨⟨t4, t5, tm⟩, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans tk).mono (by decide), by rw [tm, V.mem]⟩
  rw [t4, t5, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.PPC64LE
