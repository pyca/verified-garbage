module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Loops
public import VerifiedGarbage.Proof.Divstep.TcS
import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Words
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Packed
import VerifiedGarbage.Proof.Bignum.CrtFrame

/-!
# RSA's inverse by divsteps on x86-64: a batch

A batch (`batch_ok`) is `Divstep.batchS 59` on the window and arrays (`BS`):
the divsteps on the low words (`bWords_ok`), then `(f, g)` by `lin_ok` and
`shrP_ok` (`Divstep.shr_nat`), `(a, b)` by `lin_ok` and `mredP_ok`
(`Divstep.mredRaw_nat`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := by unfold slot hdrBytes; rfl

theorem xor_m1' (x : BitVec 64) : x ^^^ (-1 : BitVec 32).signExtend 64 = ~~~x := by
  rw [show (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]

/-- `bStart`: the low words of `f` and `g` into the window, `~d` into `rbx`, the stride into `r14`. -/
theorem bStart_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (hw1 : 2 ≤ w) (hZ : slot w 26 ≤ Z) :
    WP isa (.block bStart) s fun t =>
      t.mem = (s.mem.writeW (off B (slot w 16)) (word s.mem B (slot w 19))).writeW (off B (slot w 16 + 8))
        (word s.mem B (slot w 20)) ∧
      t.gpr .rbx = ~~~word s.mem B (slot w 16 + oD) ∧ t.gpr .r14 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      Keep [.rax, .rbx, .r14] s t := by
  have hN := hs.nowrap
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e26 := slot_eq w 26
  have e0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => by
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  unfold bStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (wa_ok 3 (r := .rax) (by decide) hdi h9) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  rw [show 16 + 3 = 19 from rfl] at a₁
  rw [show ∀ l : List Instr, ([Instr.mov .rax (.mem (at0 .rax)), .store (wm 0) .rax] ++ l) =
    [Instr.mov .rax (.mem (at0 .rax)), .store (wm 0) .rax] ++ l from fun _ => rfl, WP.block_append_iff]
  have hdi₁ : s₁.gpr .rdi = off B (slot w 16) := (k₁.gpr (by decide)).trans hdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (slot w 16)) (word s₁.mem B (slot w 19)))
    (by
      unfold wm
      have hs₁ := hs.congr k₁.2.2
      xrun [State.ea, at0, a₁, hdi₁, e0, offD, Nat.add_zero, hs₁.ld (show slot w 19 + 8 ≤ Z by omega),
        hs₁.st (show slot w 16 + 8 ≤ Z by omega)]) rfl) fun s₂ ⟨m₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wa_ok 4 (r := .rax) (by decide) ((k₂.gpr (by decide)).trans hdi₁)
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h9))) fun s₃ ⟨a₃, m₃, k₃⟩ => ?_
  rw [show 16 + 4 = 20 from rfl] at a₃
  have hdi₃ : s₃.gpr .rdi = off B (slot w 16) := ((k₂.trans k₃).gpr (by decide)).trans hdi₁
  have h9₃ : s₃.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (((k₁.trans k₂).trans k₃).gpr (by decide)).trans h9
  have o₂ : Outside B (slot w 16) 8 s.mem s₂.mem := by
    rw [m₂, m₁]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (WP.keep [.rax, .rbx, .r14] (Q := fun t =>
      t.mem = s₃.mem.writeW (off B (slot w 16 + 8)) (word s₃.mem B (slot w 20)) ∧
      t.gpr .rbx = ~~~word s₃.mem B (slot w 16 + oD) ∧ t.gpr .r14 = BitVec.ofNat 64 (8 * (w + 2)))
    (by
      unfold wm
      have hs₃ := (hs.congr k₁.2.2).congr (k₂.trans k₃).2.2
      have hrd : ∀ v : BitVec 64, (s₃.mem.writeW (off B (slot w 16 + 8)) v).readW (off B (slot w 16 + oD)) 64 =
          s₃.mem.readW (off B (slot w 16 + oD)) 64 := fun v =>
        (writeW_outside s₃.mem B v (d := slot w 16 + 8) (by omega)).word (by unfold oD; omega) (by unfold oD; omega)
      xrun [State.ea, at0, a₃, hdi₃, h9₃, e0, offD, xor_m1', hs₃.ld (show slot w 20 + 8 ≤ Z by omega),
        hs₃.st (show slot w 16 + 8 + 8 ≤ Z by omega), hs₃.ld (show slot w 16 + oD + 8 ≤ Z by unfold oD; omega), hrd]
      done) rfl) fun t ⟨⟨mt, bx, r14⟩, kt⟩ => ?_
  refine ⟨?_, ?_, r14, (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩
  · rw [mt, m₃, o₂.word (d := slot w 20) (by omega) (by omega), m₂, m₁]
  · rw [bx, m₃, o₂.word (by unfold oD; omega) (by unfold oD; omega)]

/-- `bSave`: `d` and the matrix into the window, the stride back to `r9`, `r12 := n + 1`. -/
theorem bSave_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h14 : s.gpr .r14 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hZ : slot w 16 + 64 ≤ Z) :
    WP isa (.block bSave) s fun t =>
      t.mem = ((((s.mem.writeW (off B (slot w 16 + oD)) (s.gpr .rbx)).writeW (off B (slot w 16 + oU)) (s.gpr .r9)).writeW
        (off B (slot w 16 + oV)) (s.gpr .r10)).writeW (off B (slot w 16 + oQ)) (s.gpr .r11)).writeW
        (off B (slot w 16 + oR)) (s.gpr .r12) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      Keep [.r9, .r12] s t := by
  refine WP.mono (WP.keep [.r9, .r12] (Q := fun t =>
      t.mem = ((((s.mem.writeW (off B (slot w 16 + oD)) (s.gpr .rbx)).writeW (off B (slot w 16 + oU)) (s.gpr .r9)).writeW
        (off B (slot w 16 + oV)) (s.gpr .r10)).writeW (off B (slot w 16 + oQ)) (s.gpr .r11)).writeW
        (off B (slot w 16 + oR)) (s.gpr .r12) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1)) ?_ rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  unfold bSave wm
  xrun [State.ea, hdi, offD, h14, h15, hs.st (show slot w 16 + oD + 8 ≤ Z by unfold oD; omega),
    hs.st (show slot w 16 + oU + 8 ≤ Z by unfold oU; omega), hs.st (show slot w 16 + oV + 8 ≤ Z by unfold oV; omega),
    hs.st (show slot w 16 + oQ + 8 ≤ Z by unfold oQ; omega), hs.st (show slot w 16 + oR + 8 ≤ Z by unfold oR; omega)]
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

/-! ## The arithmetic of the updates -/

/-- The sign word of the top word, as the top half of the number. -/
theorem signW_half (m : Mem) (p : Addr) (e n : Nat) :
    signW (word m p (e + 8 * n)) = if 2 ^ (64 * n) * 2 ^ 63 ≤ wv m p e (n + 1) then 2 ^ 64 - 1 else 0 := by
  unfold signW
  have hl := wv_lt m p e n
  have hx := (word m p (e + 8 * n)).isLt
  rw [wv]
  by_cases h : 2 ^ 63 ≤ (word m p (e + 8 * n)).toNat
  · have : 2 ^ (64 * n) * 2 ^ 63 ≤ 2 ^ (64 * n) * (word m p (e + 8 * n)).toNat := Nat.mul_le_mul_left _ h
    simp only [h, ↓reduceIte, show 2 ^ (64 * n) * 2 ^ 63 ≤ wv m p e n + 2 ^ (64 * n) * (word m p (e + 8 * n)).toNat by omega]
  · have : 2 ^ (64 * n) * ((word m p (e + 8 * n)).toNat + 1) ≤ 2 ^ (64 * n) * 2 ^ 63 :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add_one] at this
    simp only [h, ↓reduceIte, show ¬ 2 ^ (64 * n) * 2 ^ 63 ≤ wv m p e n + 2 ^ (64 * n) * (word m p (e + 8 * n)).toNat by omega]

/-- The low word of numbers congruent modulo `2^(64 (n + 1))`. -/
theorem low_cong' {m : Mem} {p : Addr} {e n : Nat} {x : Int}
    (h : (wv m p e (n + 1) : Int) % 2 ^ (64 * (n + 1)) = x % 2 ^ (64 * (n + 1))) :
    ((word m p e).toNat : Int) % 2 ^ 64 = x % 2 ^ 64 := by
  have hdvd : ((2 : Int) ^ 64) ∣ 2 ^ (64 * (n + 1)) := pow_dvd_pow 2 (by omega)
  have low : ((word m p e).toNat : Int) % 2 ^ 64 = (wv m p e (n + 1) : Int) % 2 ^ 64 := by
    rw [wv_succ_low]; push_cast; rw [Int.add_mul_emod_self_left]
  rw [low, ← Int.emod_emod_of_dvd _ hdvd, h, Int.emod_emod_of_dvd _ hdvd]

/-- `shrP_ok`'s result as `Divstep.shr_nat` reads it: the shift of `y = 2^59 z`. -/
theorem shr_val {m m' : Mem} {B : Addr} {eT eD n : Nat} {y z : Int}
    (hD : wv m' B eD (n + 1) = (wv m B eT (n + 1) + 2 ^ (64 * (n + 1)) * signW (word m B (eT + 8 * n))) /
      2 ^ 59 % 2 ^ (64 * (n + 1)))
    (hT : (wv m B eT (n + 1) : Int) % 2 ^ (64 * (n + 1)) = y % 2 ^ (64 * (n + 1)))
    (hy : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ y ∧ y < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int))
    (hz : y = 2 ^ 59 * z) :
    (wv m' B eD (n + 1) : Int) % 2 ^ (64 * (n + 1)) = z % 2 ^ (64 * (n + 1)) := by
  have e2 : 2 ^ (64 * (n + 1)) = 2 * (2 ^ (64 * n) * 2 ^ 63) := by rw [pow64_succ]; grind
  have hc := Divstep.shr_nat (H := 2 ^ (64 * n) * 2 ^ 63) (V := wv m B eT (n + 1)) (D := wv m' B eD (n + 1))
    (c := 2 ^ 59) (B := 2 ^ 64) (y := y) (z := z) rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (by decide))
    (by rw [← e2]; exact wv_lt _ _ _ _) (by rw [← e2]; exact_mod_cast hT) hy.1 hy.2 hz
    (by rw [hD, ← signW_half, e2])
  have e2' : (2 : Int) ^ (64 * (n + 1)) = ((2 * (2 ^ (64 * n) * 2 ^ 63) : Nat) : Int) := by
    rw [← e2]; push_cast; rfl
  rw [e2']; exact hc

/-- `mredP_ok`'s result as `Divstep.mredRaw_nat` reads it. -/
theorem mred_val {m m' : Mem} {B : Addr} {eT eD eP n p mi : Nat} {t : Int}
    (hD : wv m' B eD (n + 1) = (wv m B eT (n + 1) + 2 ^ (64 * (n + 1)) * signW (word m B (eT + 8 * n)) +
      (word m B eT).toNat * mi % 2 ^ 64 * wv m B eP n) % 2 ^ (64 * (n + 2)) / 2 ^ 64)
    (hP : wv m B eP n = p) (hT : (wv m B eT (n + 1) : Int) % 2 ^ (64 * (n + 1)) = t % 2 ^ (64 * (n + 1)))
    (hp : 0 < p) (hpA : p < 2 ^ (64 * n)) (hm : (p * mi + 1) % 2 ^ 64 = 0) (ht : |t| ≤ 2 ^ 63 * p) :
    (wv m' B eD (n + 1) : Int) % 2 ^ (64 * (n + 1)) = Divstep.mredRaw p mi t % 2 ^ (64 * (n + 1)) := by
  have eAB : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := pow64_succ n
  have eABB : 2 ^ (64 * (n + 2)) = 2 ^ (64 * n) * 2 ^ 64 * 2 ^ 64 := by rw [pow64_succ (n + 1), eAB]
  have hlow : wv m B eT (n + 1) % 2 ^ 64 = (word m B eT).toNat := by
    rw [wv_succ_low, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (word m B eT).isLt]
  have hc := Divstep.mredRaw_nat (A := 2 ^ (64 * n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := mi)
    (W := wv m B eT (n + 1)) (k := (word m B eT).toNat * mi % 2 ^ 64) (t := t)
    (E := (wv m B eT (n + 1) + 2 ^ (64 * (n + 1)) * signW (word m B (eT + 8 * n)) +
      (word m B eT).toNat * mi % 2 ^ 64 * wv m B eP n) % 2 ^ (64 * (n + 2)))
    (R := wv m' B eD (n + 1)) rfl rfl (Nat.two_pow_pos _) hp hpA hm ht (by rw [← eAB]; exact wv_lt _ _ _ _)
    (by rw [← eAB]; exact_mod_cast hT) (by rw [hlow])
    (by rw [signW_half, hP, eABB, ← eAB]) hD
  have e' : (2 : Int) ^ (64 * (n + 1)) = ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int) := by rw [← eAB]; push_cast; rfl
  rw [e']; exact hc

/-- The facts of the working space a batch's updates need. -/
structure Lay (B : Addr) (Z w n : Nat) : Prop where
  n1 : 1 ≤ n
  nw : n ≤ w
  w2 : 2 ≤ w
  w24 : w < 2 ^ 24
  z : slot w 26 ≤ Z
  nowrap : B.toNat + Z ≤ 2 ^ 64

/-- `(f, g) := (u f + v g, q f + r g) / 2^59`, from the matrix in the window. -/
theorem fgUpd_ok {s : State} {B : Addr} {Z w n : Nat} (L : Lay B Z w n) (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (n + 1)) (h15 : s.gpr .r15 = BitVec.ofNat 64 n)
    {u v q r f g z₁ z₂ : Int}
    (hu : word s.mem B (slot w 16 + oU) = BitVec.ofInt 64 u) (hv : word s.mem B (slot w 16 + oV) = BitVec.ofInt 64 v)
    (hq : word s.mem B (slot w 16 + oQ) = BitVec.ofInt 64 q) (hr : word s.mem B (slot w 16 + oR) = BitVec.ofInt 64 r)
    (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (hf : (wv s.mem B (slot w 19) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = f % 2 ^ (64 * (n + 1)))
    (hg : (wv s.mem B (slot w 20) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = g % 2 ^ (64 * (n + 1)))
    (hz₁ : u * f + v * g = 2 ^ 59 * z₁) (hz₂ : q * f + r * g = 2 ^ 59 * z₂)
    (hb₁ : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ u * f + v * g ∧ u * f + v * g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int))
    (hb₂ : -((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ q * f + r * g ∧ q * f + r * g < ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int)) :
    WP isa (seqs (lin oU oV 3 4 ++ shr 8 ++ lin oQ oR 3 4 ++ shr 4 ++ copyW 8 3)) s fun t =>
      (wv t.mem B (slot w 19) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = z₁ % 2 ^ (64 * (n + 1)) ∧
      (wv t.mem B (slot w 20) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = z₂ % 2 ^ (64 * (n + 1)) ∧
      t.gpr .rdi = off B (slot w 16) ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      Frm B [(slot w 16 + oMu, 16), (slot w 19, 16 * (w + 2)), (slot w 23, 16 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14] s t := by
  have hN := L.nowrap
  have hn1 := L.n1; have hnw := L.nw; have hw2' := L.w2; have hZ := L.z
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e20 := slot_eq w 20; have e23 := slot_eq w 23
  have e24 := slot_eq w 24; have e26 := slot_eq w 26
  have e3 := slot_eq w (16 + 3); have e4 := slot_eq w (16 + 4); have e7 := slot_eq w (16 + 7)
  have e8 := slot_eq w (16 + 8)
  have hw2 : 8 * (n + 1) ≤ 8 * (w + 2) := by omega
  have au := Int.natCast_natAbs u; have av := Int.natCast_natAbs v
  have aq := Int.natCast_natAbs q; have ar := Int.natCast_natAbs r
  have tu : (BitVec.ofInt 64 u).toInt = u := Divstep.toInt_small (by have := abs_nonneg v; omega)
  have tv : (BitVec.ofInt 64 v).toInt = v := Divstep.toInt_small (by have := abs_nonneg u; omega)
  have tq : (BitVec.ofInt 64 q).toInt = q := Divstep.toInt_small (by have := abs_nonneg r; omega)
  have tr : (BitVec.ofInt 64 r).toInt = r := Divstep.toInt_small (by have := abs_nonneg q; omega)
  rw [seqs_append_iff _ (copyW 8 3) (by simp [lin, shr]) (by simp [copyW]),
    seqs_append_iff _ (shr 4) (by simp [lin, shr]) (by simp [shr]),
    seqs_append_iff _ (lin oQ oR 3 4) (by simp [lin, shr]) (by simp [lin]),
    seqs_append_iff (lin oU oV 3 4) (shr 8) (by simp [lin]) (by simp [shr])]
  -- `t := u f + v g`.
  refine WP.mono (linP_ok (kX := 3) (kY := 4) hs hdi h9 h12 hnw L.w24 (by decide) (by decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hu, hv, tu, tv]; omega)) fun s₁ ⟨v₁, f₁, k₁⟩ => ?_
  rw [hu, hv, tu, tv, Divstep.cong_comb hf hg] at v₁
  -- `S := t / 2^59 = z₁`.
  refine WP.mono (shrP_ok (kD := 8) (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h9)
    ((k₁.gpr (by decide)).trans h15) hn1 hnw L.w24 (by omega) (by omega) (by omega)) fun s₂ ⟨v₂, r12₂, o₂, k₂⟩ => ?_
  have S₂ := shr_val v₂ v₁ hb₁ hz₁
  have k12 := k₁.trans k₂
  -- The words the second combination reads.
  have m₂ : ∀ e, (e + 8 ≤ slot w 16 + oMu ∨ slot w 19 ≤ e) → e + 8 ≤ slot w 23 → word s₂.mem B e = word s.mem B e :=
    fun e h1 h2 => by
      rw [o₂.word (by omega) (by omega), f₁.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> unfold oMu at * <;> omega) (by omega)]
  have F₂ : ∀ e, slot w 19 ≤ e → e + 8 * (n + 1) ≤ slot w 23 → wv s₂.mem B e (n + 1) = wv s.mem B e (n + 1) :=
    fun e h1 h2 => wv_congr fun i hi => m₂ _ (.inr (by omega)) (by omega)
  refine WP.mono (linP_ok (kX := 3) (kY := 4) (hs.congr k12.2.2) ((k12.gpr (by decide)).trans hdi)
    ((k12.gpr (by decide)).trans h9) r12₂ hnw L.w24 (by decide) (by decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [m₂ _ (.inl (by unfold oQ oMu; omega)) (by unfold oQ; omega), m₂ _ (.inl (by unfold oR oMu; omega)) (by unfold oR; omega), hq, hr, tq, tr]; omega))
    fun s₃ ⟨v₃, f₃, k₃⟩ => ?_
  rw [m₂ _ (.inl (by unfold oQ oMu; omega)) (by unfold oQ; omega), m₂ _ (.inl (by unfold oR oMu; omega)) (by unfold oR; omega), hq, hr, tq, tr,
    F₂ _ (by omega) (by omega), F₂ _ (by omega) (by omega), Divstep.cong_comb hf hg] at v₃
  have k13 := k12.trans k₃
  -- `G := (q f + r g) / 2^59 = z₂`.
  refine WP.mono (shrP_ok (kD := 4) (hs.congr k13.2.2) ((k13.gpr (by decide)).trans hdi)
    ((k13.gpr (by decide)).trans h9) ((k13.gpr (by decide)).trans h15) hn1 hnw L.w24 (by omega) (by omega)
    (by omega)) fun s₄ ⟨v₄, r12₄, o₄, k₄⟩ => ?_
  have G₄ := shr_val v₄ v₃ hb₂ hz₂
  have k14 := k13.trans k₄
  -- `F := S`.
  refine WP.mono (copyWP_ok (kS := 8) (kD := 3) (hs.congr k14.2.2) ((k14.gpr (by decide)).trans hdi)
    ((k14.gpr (by decide)).trans h9) r12₄ hnw L.w24 (by omega) (by omega) (by omega)) fun t ⟨vt, ot, kt⟩ => ?_
  have S₄ : wv s₄.mem B (slot w 24) (n + 1) = wv s₂.mem B (slot w 24) (n + 1) := by
    rw [o₄.wv (by omega) (by omega), f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> unfold oMu at * <;> omega) (by omega)]
  refine ⟨?_, ?_, ((k14.trans kt).gpr (by decide)).trans hdi, ((k14.trans kt).gpr (by decide)).trans h9,
    (kt.gpr (by decide)).trans r12₄, ?_, (k14.trans kt).mono (by decide)⟩
  · rw [show (16 : Nat) + 3 = 19 from rfl] at vt; rw [vt, show (16 : Nat) + 8 = 24 from rfl, S₄]; exact S₂
  · rw [ot.wv (by omega) (by omega)]; exact G₄
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    obtain ⟨xW, xF, xT⟩ := hx
    rw [ot x (by omega), o₄ x (by omega), f₃ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      unfold oMu at *; omega), o₂ x (by omega), f₁ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      unfold oMu at *; omega)]

end VG.Proof.Rsa.X86_64.InvB
