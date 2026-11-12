module
-- separate module: it imports the batches' and the end's algebra (`Proof/Divstep/TcS.lean`), which only the registrations reach

public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import VerifiedGarbage.Proof.Divstep.TcSBounds
import VerifiedGarbage.Proof.Rsa.Divstep.Bound
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
public import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbOps
public import VerifiedGarbage.Proof.Divstep.TcS
public import Mathlib.Algebra.Order.Ring.Abs
public import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.NormNum

/-!
# The batched inverse on RISC-V: the batches

`loop_ok`: `3 ν + 2` batches from the start of the inversion, counted in
`s7`, as `Proof/Divstep/TcS.lean`'s `invRunS 59`; `loopG_ok`: as many
batches of `f` and `g` alone.
-/

@[expose] public section

/-!
# The batched inverse on RISC-V: a batch

A batch (`batch_ok`) is `Proof/Divstep/TcS.lean`'s `batchS 59` on the window
and the arrays (`BS`, numbers modulo `2^(64 (ν + 1))`), as x86-64's
(`Proof/Rsa/X86_64/InvB/Batch.lean`): 59 divsteps on the low words
(`head_ok`), then `(f, g)` by `lin_ok` and `shr_ok` (`Divstep.shr_nat`),
`(a, b)` by `lin_ok` and `mred_ok` (`Divstep.mredRaw_nat`).
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.RISCV64.RegUpd
open VG.Proof.Divstep (MSt msteps)

/-! ## Frames -/

/-- A word of `≤ 8` bytes inside an array outside a frame. -/
theorem keep_word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keys.Frame B w js ds m m') {j o b : Nat} (hb : o + b / 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    m'.readW (off B (arr w j + o)) b = m.readW (off B (arr w j + o)) b := by
  refine Mem.readW_congr fun i hi => h _ fun r hr => ?_
  rw [ofs_off B (by omega)]
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; omega
  · have := hd d hd'; have : hdr ≤ arr w j := hdr_le_arr w j; dsimp only; omega

/-- The first `k` words (`8 k ≤ S w`) of an array outside a frame. -/
theorem keep_wv {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem}
    (h : Keys.Frame B w js [] m m') {j k : Nat} (hk : 8 * k ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (fit : arr w j + S w ≤ 2 ^ 64) :
    wordsVal m' B (arr w j) k = wordsVal m B (arr w j) k :=
  h.words (fun x hx => by have := arr_disj (w := w) (hj x hx); omega) (by simp) (by omega)

/-- A number of `k + 1` words is its low word modulo `2^59`. -/
theorem low59 {m : Mem} {B : Addr} {d k : Nat} {x : Int}
    (h : (wordsVal m B d (k + 1) : Int) % 2 ^ (64 * (k + 1)) = x % 2 ^ (64 * (k + 1))) :
    ((word m B d).toNat : Int) % 2 ^ 59 = x % 2 ^ 59 := by
  have hW : wordsVal m B d (k + 1) = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) k := rfl
  have hdvd : (2 : Int) ^ 59 ∣ 2 ^ (64 * (k + 1)) := pow_dvd_pow 2 (by omega)
  rw [← Int.emod_emod_of_dvd x hdvd, ← h, Int.emod_emod_of_dvd _ hdvd, hW]
  push_cast
  omega

/-! ## The divsteps -/

theorem Outside.readW64 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    m'.readW (off base d) 64 = m.readW (off base d) 64 :=
  Mem.readW_congr fun _ _ => h _ (by rw [ofs_off base (by omega)]; omega)

/-- A 64-bit store changes only its 8 bytes. -/
theorem writeW64_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- `save`: `d` and the matrix stored to the window. -/
theorem save_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block save) t fun u => (u.mem = ((((t.mem.writeW (off B (arr w aW)) (t.gpr .t6)).writeW
      (off B (arr w aW + 8)) (t.gpr .t1)).writeW (off B (arr w aW + 16)) (t.gpr .t2)).writeW
      (off B (arr w aW + 24)) (t.gpr .t3)).writeW (off B (arr w aW + 32)) (t.gpr .t4)) ∧ Keep [.a4] t u := by
  have hW : aW < N := by have := h.room; unfold aW; omega
  have fW := h.ws.arr_fit hW
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  have := arr_al w aW
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hs := h.ws.scr
  brun [exec_li, save, List.append_assoc, (show aW < 2048 by decide), wD, wU, wV, wQ, wR, runBlock_ptr B w, h.ws.s10, h.ws.s11, exec_store_d,
    hs.st (show arr w aW + 8 ≤ Z by omega), hs.st (show arr w aW + 8 + 8 ≤ Z by omega),
    hs.st (show arr w aW + 16 + 8 ≤ Z by omega), hs.st (show arr w aW + 24 + 8 ≤ Z by omega),
    hs.st (show arr w aW + 32 + 8 ≤ Z by omega),
    hs.al8 (show arr w aW + 8 ≤ Z by omega) (by omega), hs.al8 (show arr w aW + 8 + 8 ≤ Z by omega) (by omega),
    hs.al8 (show arr w aW + 16 + 8 ≤ Z by omega) (by omega),
    hs.al8 (show arr w aW + 24 + 8 ≤ Z by omega) (by omega),
    hs.al8 (show arr w aW + 32 + 8 ≤ Z by omega) (by omega)]

/-- The words of `save`'s stores, read back. -/
theorem save_read (m : Mem) (B : Addr) (d : Nat) (hd : d + 40 ≤ 2 ^ 64) (a b c e f : BitVec 64) :
    let m' := ((((m.writeW (off B d) a).writeW (off B (d + 8)) b).writeW (off B (d + 16)) c).writeW
      (off B (d + 24)) e).writeW (off B (d + 32)) f
    m'.readW (off B d) 64 = a ∧ m'.readW (off B (d + 8)) 64 = b ∧ m'.readW (off B (d + 16)) 64 = c ∧
      m'.readW (off B (d + 24)) 64 = e ∧ m'.readW (off B (d + 32)) 64 = f ∧ Outside B d 40 m m' := by
  intro m'
  have o1 := writeW64_outside m B (d := d) a (by omega)
  have o2 := writeW64_outside (m.writeW (off B d) a) B (d := d + 8) b (by omega)
  have o3 := writeW64_outside ((m.writeW (off B d) a).writeW (off B (d + 8)) b) B (d := d + 16) c (by omega)
  have o4 := writeW64_outside (((m.writeW (off B d) a).writeW (off B (d + 8)) b).writeW (off B (d + 16)) c) B
    (d := d + 24) e (by omega)
  have o5 := writeW64_outside ((((m.writeW (off B d) a).writeW (off B (d + 8)) b).writeW (off B (d + 16)) c).writeW
    (off B (d + 24)) e) B (d := d + 32) f (by omega)
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _, ?_⟩
  · rw [Outside.readW64 o5 (by omega) (by omega), Outside.readW64 o4 (by omega) (by omega),
      Outside.readW64 o3 (by omega) (by omega), Outside.readW64 o2 (by omega) (by omega),
      Mem.readW_writeW_self64]
  · rw [Outside.readW64 o5 (by omega) (by omega), Outside.readW64 o4 (by omega) (by omega),
      Outside.readW64 o3 (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [Outside.readW64 o5 (by omega) (by omega), Outside.readW64 o4 (by omega) (by omega),
      Mem.readW_writeW_self64]
  · rw [Outside.readW64 o5 (by omega) (by omega), Mem.readW_writeW_self64]
  · exact ((((o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))).trans
      (o3.mono (by omega) (by omega))).trans (o4.mono (by omega) (by omega))).trans (o5.mono (by omega) (by omega))


/-- `d`, `f` and `g` of the inversion in the window and the arrays, `f` and `g`
modulo `2^(64 (ν + 1))`. -/
structure BG (s : State) (B : Addr) (w n : Nat) (I : Divstep.IState) : Prop where
  d : s.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 I.d
  f : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1))
  g : (wordsVal s.mem B (arr w aG) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.g % 2 ^ (64 * (nu n + 1))

/-- The state of the inversion: `BG`, and `a`, `b` modulo `2^(64 (ν + 1))`,
`-p⁻¹ mod 2^64` in the window and `p` in array 2 with a zero word `ν`. -/
structure BS (s : State) (B : Addr) (w n p iv : Nat) (I : Divstep.IState) : Prop extends BG s B w n I where
  a : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.a % 2 ^ (64 * (nu n + 1))
  b : (wordsVal s.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.b % 2 ^ (64 * (nu n + 1))
  iv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv
  P : wordsVal s.mem B (arr w aMz) (nu n) = p
  P1 : wordsVal s.mem B (arr w aMz) (nu n + 1) = p

/-- The words the batch's divsteps leave. -/
abbrev mat (I : Divstep.IState) : MSt := msteps 59 (MSt.init I.d I.f I.g)

/-- `start`, 59 divsteps and `save`: `d` and the matrix of 59 divsteps from
`(d, f, g)` in the window. -/
theorem head_ok {s : State} {B : Addr} {Z w N n : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n) (hst : BG s B w n I) (hN : N ≤ 256)
    (hd : |I.d| + 2 * 59 < 2 ^ 62) (hf : I.f % 2 = 1) :
    WP isa (.block (start ++ wsteps 59 ++ save)) s fun t => Ctx t B Z w N n ∧
      Keys.Frame B w [aW] [] s.mem t.mem ∧ Outside B (arr w aW) 40 s.mem t.mem ∧
      t.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 (mat I).d ∧
      t.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat I).u ∧
      t.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat I).v ∧
      t.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat I).q ∧
      t.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat I).r ∧ Keep kRegs s t := by
  have hW : aW < N := by have := h.room; unfold aW; omega
  have hFN : aF < N := by have := h.room; unfold aF; omega
  have hGN : aG < N := by have := h.room; unfold aG; omega
  have fW := h.ws.arr_fit hW
  have fF := h.ws.arr_fit hFN
  have fG := h.ws.arr_fit hGN
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  have hs := h.ws.scr
  have := arr_al w aW
  have := arr_al w aF
  have := arr_al w aG
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The start: the low words, `d` and the identity.
  have hs1 : WP isa (.block start) s fun t => (regsW t = ⟨BitVec.ofInt 64 I.d,
      word s.mem B (arr w aF), word s.mem B (arr w aG),
      BitVec.ofNat 64 1, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 1⟩ ∧ t.mem = s.mem) ∧
      Keep kRegs s t := by
    have hd0 : s.mem.readW (off B (arr w aW)) 64 = BitVec.ofInt 64 I.d := by
      simpa only [wD, Nat.add_zero] using hst.d
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, start, ldW, List.append_assoc, (show aW < 2048 by decide), (show aF < 2048 by decide),
      (show aG < 2048 by decide), regsW, wD, runBlock_ptr B w, h.ws.s10, h.ws.s11, fin64_exec_li_zero,
      hs.ld (show arr w aF + 8 ≤ Z by omega), hs.ld (show arr w aG + 8 ≤ Z by omega),
      hs.ld (show arr w aW + 8 ≤ Z by omega), hs.al8 (show arr w aF + 8 ≤ Z by omega) (by omega),
      hs.al8 (show arr w aG + 8 ≤ Z by omega) (by omega), hs.al8 (show arr w aW + 8 ≤ Z by omega) (by omega),
      hd0]
    try rfl
  refine WP.mono hs1 fun t1 ⟨⟨r1, m1⟩, k1⟩ => ?_
  refine WP.mono (wsteps_ok 59 t1) fun t2 ⟨⟨r2, m2⟩, k2⟩ => ?_
  have h2 := h.of_keep (Keep.trans' k1 k2)
  -- The words of the divsteps.
  have rel : (regsW t1).rel (MSt.init I.d I.f I.g) 59 := by
    rw [r1]
    exact ⟨rfl, rfl, rfl, rfl, rfl, low59 hst.f, low59 hst.g⟩
  have R := Divstep.wsteps_rel (by decide) rel (by simpa [MSt.init] using hd) hf 59 (Nat.le_refl _)
  rw [← r2] at R
  obtain ⟨Rd, Ru, Rv, Rq, Rr, -, -⟩ := R
  refine WP.mono (save_ok h2) fun t3 ⟨m3, k3⟩ => ?_
  obtain ⟨e0, e1, e2, e3, e4, out⟩ := save_read t2.mem B (arr w aW) (by omega) (t2.gpr .t6) (t2.gpr .t1)
    (t2.gpr .t2) (t2.gpr .t3) (t2.gpr .t4)
  rw [← m3] at e0 e1 e2 e3 e4 out
  rw [m2, m1] at out
  have k : Keep kRegs s t3 := Keep.trans' (Keep.trans' k1 k2) (k3.mono (by decide))
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega)
    (by simp), out, ?_, ?_, ?_, ?_, ?_, k⟩
  · simpa only [wD, Nat.add_zero] using e0.trans Rd
  · exact e1.trans Ru
  · exact e2.trans Rv
  · exact e3.trans Rq
  · exact e4.trans Rr

/-! ## The arithmetic of the updates -/

theorem pow_succ64 (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- `shr_ok`'s result as `Divstep.shr_nat` reads it: the shift of `y = 2^59 z`. -/
theorem shr_val {D V k : Nat} {y z : Int}
    (hD : D = (V + 2 * (2 ^ (64 * k) * 2 ^ 63) * (if 2 ^ (64 * k) * 2 ^ 63 ≤ V then 2 ^ 64 - 1 else 0)) /
      2 ^ 59 % (2 * (2 ^ (64 * k) * 2 ^ 63)))
    (hV : V < 2 ^ (64 * (k + 1)))
    (hT : (V : Int) % 2 ^ (64 * (k + 1)) = y % 2 ^ (64 * (k + 1)))
    (hy : -((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) ≤ y ∧ y < ((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int))
    (hz : y = 2 ^ 59 * z) :
    (D : Int) % 2 ^ (64 * (k + 1)) = z % 2 ^ (64 * (k + 1)) := by
  have e2 : 2 ^ (64 * (k + 1)) = 2 * (2 ^ (64 * k) * 2 ^ 63) := by
    rw [pow_succ64, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ac_rfl
  have e2' : (2 : Int) ^ (64 * (k + 1)) = ((2 * (2 ^ (64 * k) * 2 ^ 63) : Nat) : Int) := by
    rw [← e2]; push_cast; rfl
  rw [e2'] at hT ⊢
  exact Divstep.shr_nat (H := 2 ^ (64 * k) * 2 ^ 63) (V := V) (D := D) (c := 2 ^ 59) (B := 2 ^ 64)
    rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (by rw [← e2]; exact hV) hT hy.1 hy.2 hz hD

/-- `mred_ok`'s result as `Divstep.mredRaw_nat` reads it. -/
theorem mred_val {R W w0 k p iv : Nat} {t : Int}
    (hR : R = (W + 2 ^ (64 * k) * 2 ^ 64 * (if 2 ^ (64 * k) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) +
      w0 * iv % 2 ^ 64 * p) % (2 ^ (64 * k) * 2 ^ 64 * 2 ^ 64) / 2 ^ 64)
    (hw0 : W % 2 ^ 64 = w0) (hW : W < 2 ^ (64 * (k + 1)))
    (hT : (W : Int) % 2 ^ (64 * (k + 1)) = t % 2 ^ (64 * (k + 1)))
    (hp : 0 < p) (hpA : p < 2 ^ (64 * k)) (hm : (p * iv + 1) % 2 ^ 64 = 0) (ht : |t| ≤ 2 ^ 63 * p) :
    (R : Int) % 2 ^ (64 * (k + 1)) = Divstep.mredRaw p iv t % 2 ^ (64 * (k + 1)) := by
  have eAB : (2 : Int) ^ (64 * (k + 1)) = ((2 ^ (64 * k) * 2 ^ 64 : Nat) : Int) := by
    rw [← pow_succ64]; push_cast; rfl
  rw [eAB] at hT ⊢
  exact Divstep.mredRaw_nat (A := 2 ^ (64 * k)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := iv) (W := W)
    (k := w0 * iv % 2 ^ 64) (t := t)
    (E := (W + 2 ^ (64 * k) * 2 ^ 64 * (if 2 ^ (64 * k) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) +
      w0 * iv % 2 ^ 64 * p) % (2 ^ (64 * k) * 2 ^ 64 * 2 ^ 64))
    (R := R) rfl rfl (Nat.two_pow_pos _) hp hpA hm ht (by rw [← pow_succ64]; exact hW) hT
    (by rw [hw0]) rfl hR

/-- A batch's combination of `f` and `g` of at most `2^(64 ν + 3)`, in the
half range of `ν + 1` words. -/
theorem comb_half {u v f g : Int} {k : Nat} (huv : |u| + |v| ≤ 2 ^ 59)
    (hf : |f| ≤ 2 ^ (64 * k) * 2 ^ 3) (hg : |g| ≤ 2 ^ (64 * k) * 2 ^ 3) :
    -((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) ≤ u * f + v * g ∧
      u * f + v * g < ((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) := by
  have := Divstep.comb_le huv hf hg
  rw [abs_le] at this
  have hA : (0 : Int) < 2 ^ (64 * k) := by positivity
  push_cast
  constructor <;> nlinarith

/-- The coefficients of a batch are at most `2^61`. -/
theorem natAbs61 {u v : Int} (h : |u| + |v| ≤ 2 ^ 59) : u.natAbs ≤ 2 ^ 61 ∧ v.natAbs ≤ 2 ^ 61 := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h; omega

/-! ## The updates -/

/-- `updateG`: the new `f` and `g` from the matrix in the window. -/
theorem updateG_ok {s : State} {B : Addr} {Z w N n : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hf : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1)))
    (hg : (wordsVal s.mem B (arr w aG) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.g % 2 ^ (64 * (nu n + 1)))
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat I).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat I).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat I).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat I).r)
    (hodd : I.f % 2 = 1) (hF : |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3) :
    WP isa updateG s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aT1, aT2, aF, aG] [] s.mem t.mem ∧
      (wordsVal t.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        ((mat I).u * I.f + (mat I).v * I.g) / 2 ^ 59 % 2 ^ (64 * (nu n + 1)) ∧
      (wordsVal t.mem B (arr w aG) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        ((mat I).q * I.f + (mat I).r * I.g) / 2 ^ 59 % 2 ^ (64 * (nu n + 1)) ∧
      Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨ef, eg⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hodd 59
  have z₁ : (mat I).u * I.f + (mat I).v * I.g = 2 ^ 59 * (((mat I).u * I.f + (mat I).v * I.g) / 2 ^ 59) := by
    rw [← ef, Int.mul_ediv_cancel_left _ (by norm_num)]
  have z₂ : (mat I).q * I.f + (mat I).r * I.g = 2 ^ 59 * (((mat I).q * I.f + (mat I).r * I.g) / 2 ^ 59) := by
    rw [← eg, Int.mul_ediv_cancel_left _ (by norm_num)]
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have nW : aW < N := by unfold aW; omega
  have w8 : ∀ o, o + 8 ≤ 48 → o + 64 / 8 ≤ S w := fun o ho => by have := h.wbig; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  simp only [updateG, seqs]
  -- `u f + v g` and `q f + r g`.
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h n1 nF nG hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hU hV (natAbs61 bu).1 (natAbs61 bu).2) fun t1 ⟨h1, K1, e1, k1⟩ => ?_
  rw [Divstep.cong_comb hf hg] at e1
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h1 n2 nF nG hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hQ)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hR)
    (natAbs61 bq).1 (natAbs61 bq).2) fun t2 ⟨h2, K2, e2, k2⟩ => ?_
  rw [keep_wv K1 hk (by decide) (fit _ nF), keep_wv K1 hk (by decide) (fit _ nG),
    Divstep.cong_comb hf hg] at e2
  -- The new `f` and `g`.
  rw [WP.seq_iff]
  refine WP.mono (shr_ok h2 nF n1 hN (by decide)) fun t3 ⟨h3, K3, e3, k3⟩ => ?_
  refine WP.mono (shr_ok h3 nG n2 hN (by decide)) fun t4 ⟨h4, K4, e4, k4⟩ => ?_
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' k1 k2) k3) k4
  rw [keep_wv K2 hk (by decide) (fit _ n1)] at e3
  rw [keep_wv K3 hk (by decide) (fit _ n2)] at e4
  refine ⟨h.of_keep k,
    (K1.mono (by simp)).trans ((K2.mono (by simp)).trans ((K3.mono (by simp)).trans (K4.mono (by simp)))),
    ?_, ?_, k⟩
  · rw [keep_wv K4 hk (by decide) (fit _ nF)]
    exact shr_val e3 (wordsVal_lt _ _ _ _) e1 (comb_half bu hF hG) z₁
  · exact shr_val e4 (wordsVal_lt _ _ _ _) e2 (comb_half bq hF hG) z₂

/-- `updateAB`: the new `a` and `b` from the matrix in the window. -/
theorem updateAB_ok {s : State} {B : Addr} {Z w N n p iv : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hA : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.a % 2 ^ (64 * (nu n + 1)))
    (hB : (wordsVal s.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.b % 2 ^ (64 * (nu n + 1)))
    (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) (hP : wordsVal s.mem B (arr w aMz) (nu n) = p)
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat I).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat I).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat I).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat I).r)
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) (hb : -(p : Int) < I.b ∧ I.b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * nu n)) (hm : (p * iv + 1) % 2 ^ 64 = 0) :
    WP isa updateAB s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aT1, aT2, aA, aB] [] s.mem t.mem ∧
      (wordsVal t.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        Divstep.mredRaw p iv ((mat I).u * I.a + (mat I).v * I.b) % 2 ^ (64 * (nu n + 1)) ∧
      (wordsVal t.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        Divstep.mredRaw p iv ((mat I).q * I.a + (mat I).r * I.b) % 2 ^ (64 * (nu n + 1)) ∧
      Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  have ha2 : |I.a| ≤ 2 * p := abs_le.mpr ⟨by omega, by omega⟩
  have hb2 : |I.b| ≤ 2 * p := abs_le.mpr ⟨by omega, by omega⟩
  have ht₁ := Divstep.comb_le2 (by norm_num) (by exact_mod_cast hp) bu ha2 hb2
  have ht₂ := Divstep.comb_le2 (by norm_num) (by exact_mod_cast hp) bq ha2 hb2
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have nM : aMz < N := by unfold aMz; omega
  have nW : aW < N := by unfold aW; omega
  have w8 : ∀ o, o + 8 ≤ 48 → o + 64 / 8 ≤ S w := fun o ho => by have := h.wbig; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  simp only [updateAB, seqs]
  -- `u a + v b` and `q a + r b`.
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h n1 nA nB hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hU hV (natAbs61 bu).1 (natAbs61 bu).2) fun t1 ⟨h1, K1, e1, k1⟩ => ?_
  rw [Divstep.cong_comb hA hB] at e1
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h1 n2 nA nB hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hQ)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hR)
    (natAbs61 bq).1 (natAbs61 bq).2) fun t2 ⟨h2, K2, e2, k2⟩ => ?_
  rw [keep_wv K1 hk (by decide) (fit _ nA), keep_wv K1 hk (by decide) (fit _ nB),
    Divstep.cong_comb hA hB] at e2
  have K12 : Keys.Frame B w [aT1, aT2] [] s.mem t2.mem := (K1.mono (by simp)).trans (K2.mono (by simp))
  -- The reductions.
  rw [WP.seq_iff]
  refine WP.mono (mred_ok h2 n1 nA hN (by decide)) fun t3 ⟨h3, K3, e3, k3⟩ => ?_
  refine WP.mono (mred_ok h3 n2 nB hN (by decide)) fun t4 ⟨h4, K4, e4, k4⟩ => ?_
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' k1 k2) k3) k4
  have P2 : wordsVal t2.mem B (arr w aMz) (nu n) = p := by rw [keep_wv K12 hk0 (by decide) (fit _ nM)]; exact hP
  have P3 : wordsVal t3.mem B (arr w aMz) (nu n) = p := by rw [keep_wv K3 hk0 (by decide) (fit _ nM)]; exact P2
  have iv2 : (t2.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv := by
    rw [keep_word K12 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hiv
  have iv3 : (t3.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv := by
    rw [keep_word K3 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact iv2
  rw [P2, iv2] at e3
  rw [P3, iv3] at e4
  rw [← keep_wv K2 hk (by decide) (fit _ n1)] at e1
  rw [← keep_wv K3 hk (by decide) (fit _ n2)] at e2
  have w0 : ∀ (m : Mem) (d : Nat), wordsVal m B d (nu n + 1) % 2 ^ 64 = (word m B d).toNat := fun m d => by
    show ((word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) (nu n)) % 2 ^ 64 = _
    have := (word m B d).isLt; omega
  refine ⟨h.of_keep k,
    (K12.mono (by simp)).trans ((K3.mono (by simp)).trans (K4.mono (by simp))), ?_, ?_, k⟩
  · rw [keep_wv K4 hk (by decide) (fit _ nA)]
    exact mred_val e3 (w0 _ _) (wordsVal_lt _ _ _ _) e1 hp hpA hm ht₁
  · exact mred_val e4 (w0 _ _) (wordsVal_lt _ _ _ _) e2 hp hpA hm ht₂

/-! ## A batch -/

/-- The count of the batches left, decremented. -/
theorem dec_ok {t : State} {c : Nat} (h7 : t.gpr .s7 = BitVec.ofNat 64 (c + 1)) :
    WP isa (.block [.addi .s7 .s7 (-1)]) t fun u =>
      (u.gpr .s7 = BitVec.ofNat 64 c ∧ u.mem = t.mem) ∧ Keep [.s7] t u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [exec_li, h7]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem batchS_eq (p iv : Int) (I : Divstep.IState) : Divstep.batchS 59 p iv I =
    ⟨(mat I).d, ((mat I).u * I.f + (mat I).v * I.g) / 2 ^ 59, ((mat I).q * I.f + (mat I).r * I.g) / 2 ^ 59,
      Divstep.mredRaw p iv ((mat I).u * I.a + (mat I).v * I.b),
      Divstep.mredRaw p iv ((mat I).q * I.a + (mat I).r * I.b)⟩ := rfl

/-- A batch: `Divstep.batchS 59`, and the count of the batches left, `c`, in `s7`. -/
theorem batch_ok {s : State} {B : Addr} {Z w N n c p iv : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (c + 1)) (hst : BS s B w n p iv I)
    (hN : N ≤ 256) (hd : |I.d| + 2 * 59 < 2 ^ 62) (hodd : I.f % 2 = 1)
    (hF : |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3)
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) (hb : -(p : Int) < I.b ∧ I.b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * nu n)) (hm : (p * iv + 1) % 2 ^ 64 = 0) :
    WP isa batch s fun t => Ctx t B Z w N n ∧ BS t B w n p iv (Divstep.batchS 59 p iv I) ∧
      t.gpr .s7 = BitVec.ofNat 64 c ∧
      Keys.Frame B w [aF, aG, aA, aB, aT1, aT2, aW] [] s.mem t.mem ∧ Keep (.s7 :: kRegs) s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have := h.nuw
  have hnw := h.ws.nowrap
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nW : aW < N := by unfold aW; omega
  have nM : aMz < N := by unfold aMz; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  simp only [batch, seqs, update]
  rw [WP.seq_iff]
  refine WP.mono (head_ok h hst.toBG hN hd hodd) fun t1 ⟨h1, K1, out1, d1, u1, v1, q1, r1, k1⟩ => ?_
  have fW := fit _ nW
  have iv1 : (t1.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv := by
    rw [Outside.readW64 out1 (by unfold wIv; omega) (by unfold wIv; omega)]; exact hst.iv
  have kv1 : ∀ j, j ≠ aW → j < N → ∀ k, 8 * k ≤ S w → wordsVal t1.mem B (arr w j) k = wordsVal s.mem B (arr w j) k :=
    fun j hj hjN k hk => keep_wv K1 hk (by simp [Ne.symm hj]) (fit _ hjN)
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (updateG_ok h1 hN (by rw [kv1 _ (by decide) nF _ hk]; exact hst.f)
    (by rw [kv1 _ (by decide) nG _ hk]; exact hst.g) u1 v1 q1 r1 hodd hF hG) fun t2 ⟨h2, K2, ef, eg, k2⟩ => ?_
  have wd2 : ∀ o, o + 8 ≤ 48 → t2.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => keep_word K2 (by omega) (by decide) (by simp) (fit _ nW)
  have kv2 : ∀ j, j ≠ aT1 → j ≠ aT2 → j ≠ aF → j ≠ aG → j < N → ∀ k, 8 * k ≤ S w →
      wordsVal t2.mem B (arr w j) k = wordsVal t1.mem B (arr w j) k :=
    fun j h1 h2 h3 h4 hjN k hk => keep_wv K2 hk (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]) (fit _ hjN)
  refine WP.mono (updateAB_ok h2 hN
    (by rw [kv2 _ (by decide) (by decide) (by decide) (by decide) nA _ hk, kv1 _ (by decide) nA _ hk]; exact hst.a)
    (by rw [kv2 _ (by decide) (by decide) (by decide) (by decide) nB _ hk, kv1 _ (by decide) nB _ hk]; exact hst.b)
    (by rw [wd2 _ (by decide)]; exact iv1)
    (by rw [kv2 _ (by decide) (by decide) (by decide) (by decide) nM _ hk0, kv1 _ (by decide) nM _ hk0]; exact hst.P)
    (by rw [wd2 _ (by decide)]; exact u1) (by rw [wd2 _ (by decide)]; exact v1)
    (by rw [wd2 _ (by decide)]; exact q1) (by rw [wd2 _ (by decide)]; exact r1)
    ha hb hp hpA hm) fun t3 ⟨h3, K3, ea, eb, k3⟩ => ?_
  have wd3 : ∀ o, o + 8 ≤ 48 → t3.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => (keep_word K3 (by omega) (by decide) (by simp) (fit _ nW)).trans (wd2 o ho)
  have kv3 : ∀ j, j ≠ aT1 → j ≠ aT2 → j ≠ aA → j ≠ aB → j < N → ∀ k, 8 * k ≤ S w →
      wordsVal t3.mem B (arr w j) k = wordsVal t2.mem B (arr w j) k :=
    fun j h1 h2 h3 h4 hjN k hk => keep_wv K3 hk (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]) (fit _ hjN)
  have s73 : t3.gpr .s7 = BitVec.ofNat 64 (c + 1) :=
    ((Keep.trans' (Keep.trans' k1 k2) k3).gpr (by decide)).trans h7
  refine WP.mono (dec_ok s73) fun t4 ⟨⟨r7, m4⟩, k4⟩ => ?_
  have k : Keep (.s7 :: kRegs) s t4 :=
    Keep.trans' ((Keep.trans' (Keep.trans' k1 k2) k3).mono (by decide)) (k4.mono (by decide))
  rw [batchS_eq]
  refine ⟨⟨h3.ws.of_keep k4, (k4.gpr (by decide)).trans h3.s8, h.npos, h.nw, h.room, h.wbig⟩,
    ⟨⟨?_, ?_, ?_⟩, by rw [m4]; exact ea, by rw [m4]; exact eb, ?_, ?_, ?_⟩, r7,
    by rw [m4]; exact (K1.mono (by simp)).trans ((K2.mono (by simp)).trans (K3.mono (by simp))), k⟩
  · rw [m4, wd3 _ (by decide)]; dsimp only; exact d1
  · rw [m4, kv3 _ (by decide) (by decide) (by decide) (by decide) nF _ hk]; exact ef
  · rw [m4, kv3 _ (by decide) (by decide) (by decide) (by decide) nG _ hk]; exact eg
  · rw [m4, wd3 _ (by decide)]; exact iv1
  · rw [m4, kv3 _ (by decide) (by decide) (by decide) (by decide) nM _ hk0,
      kv2 _ (by decide) (by decide) (by decide) (by decide) nM _ hk0, kv1 _ (by decide) nM _ hk0]
    exact hst.P
  · rw [m4, kv3 _ (by decide) (by decide) (by decide) (by decide) nM _ hk,
      kv2 _ (by decide) (by decide) (by decide) (by decide) nM _ hk, kv1 _ (by decide) nM _ hk]
    exact hst.P1

/-- A batch of `f` and `g` alone: the next `d`, `f` and `g`. -/
theorem batchG_ok {s : State} {B : Addr} {Z w N n c : Nat} {p iv : Int} {I : Divstep.IState}
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (c + 1)) (hst : BG s B w n I)
    (hN : N ≤ 256) (hd : |I.d| + 2 * 59 < 2 ^ 62) (hodd : I.f % 2 = 1)
    (hF : |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3) :
    WP isa batchG s fun t => Ctx t B Z w N n ∧ BG t B w n (Divstep.batchS 59 p iv I) ∧
      t.gpr .s7 = BitVec.ofNat 64 c ∧
      Keys.Frame B w [aF, aG, aT1, aT2, aW] [] s.mem t.mem ∧ Keep (.s7 :: kRegs) s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have := h.nuw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  simp only [batchG, seqs]
  rw [WP.seq_iff]
  refine WP.mono (head_ok h hst hN hd hodd) fun t1 ⟨h1, K1, _, d1, u1, v1, q1, r1, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (updateG_ok h1 hN (by rw [keep_wv K1 hk (by decide) (fit _ nF)]; exact hst.f)
    (by rw [keep_wv K1 hk (by decide) (fit _ nG)]; exact hst.g) u1 v1 q1 r1 hodd hF hG)
    fun t2 ⟨h2, K2, ef, eg, k2⟩ => ?_
  have s72 : t2.gpr .s7 = BitVec.ofNat 64 (c + 1) := ((Keep.trans' k1 k2).gpr (by decide)).trans h7
  refine WP.mono (dec_ok s72) fun t3 ⟨⟨r7, m3⟩, k3⟩ => ?_
  have k : Keep (.s7 :: kRegs) s t3 := Keep.trans' ((Keep.trans' k1 k2).mono (by decide)) (k3.mono (by decide))
  rw [batchS_eq]
  refine ⟨⟨h2.ws.of_keep k3, (k3.gpr (by decide)).trans h2.s8, h.npos, h.nw, h.room, h.wbig⟩,
    ⟨?_, by rw [m3]; exact ef, by rw [m3]; exact eg⟩, r7,
    by rw [m3]; exact (K1.mono (by simp)).trans (K2.mono (by simp)), k⟩
  rw [m3, keep_word K2 (by unfold wD; omega) (by decide) (by simp) (fit _ nW)]; dsimp only; exact d1

end VG.Proof.Rsa.RISCV64.InvBatch

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.Divstep (oddInput)

theorem Ctx.of_keep7 {s t : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n)
    (k : Keep (.s7 :: kRegs) s t) : Ctx t B Z w N n :=
  ⟨h.ws.of_keep k, (k.gpr (by decide)).trans h.s8, h.npos, h.nw, h.room, h.wbig⟩

/-- The bounds of a batch from the run's (`Divstep.invRunS_bounds`, `M = 2^(64 ν + 1)`). -/
theorem run_bounds {n p iv x k : Nat} (odd : p % 2 = 1) (hinv : (p * iv + 1) % 2 ^ 64 = 0)
    (pc : p < 2 ^ (64 * nu n)) (xc : x < 2 * 2 ^ (64 * nu n)) :
    let I := Divstep.invRunS 59 p iv x k
    |I.d| ≤ 1 + 2 * (59 * k : Nat) ∧ I.f % 2 = 1 ∧ |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3 ∧
      |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3 ∧ (-(p : Int) < I.a ∧ I.a < 2 * p) ∧ (-(p : Int) < I.b ∧ I.b < 2 * p) := by
  intro I
  have hmI : ((p : Int) * (iv : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hinv
  have hM8 : (2 * 2 ^ (64 * nu n) : Int) ≤ 2 ^ (64 * nu n) * 2 ^ 3 := by
    have : 2 * 2 ^ (64 * nu n) ≤ 2 ^ (64 * nu n) * 2 ^ 3 := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by decide)
    exact_mod_cast this
  obtain ⟨bd, bf1, bf, bg, ba0, ba1, bb0, bb1⟩ := Divstep.invRunS_bounds (N := 59) (by decide) (p := p) (m := iv)
    (x := x) (M := 2 * 2 ^ (64 * nu n)) (by exact_mod_cast odd) (by omega) hmI (Int.natCast_nonneg _)
    (by have : p ≤ 2 * 2 ^ (64 * nu n) := by omega
        exact_mod_cast this)
    (by have : x ≤ 2 * 2 ^ (64 * nu n) := by omega
        exact_mod_cast this) k
  exact ⟨bd, bf1, le_trans bf hM8, le_trans bg hM8, ⟨ba0, ba1⟩, ⟨bb0, bb1⟩⟩

/-- After `k` batches. -/
def LoopAt (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2 - k) ∧
    BS t B w n p iv (Divstep.invRunS 59 p iv x k) ∧
    Keys.Frame B w [aF, aG, aA, aB, aT1, aT2, aW] [] s₀.mem t.mem ∧ Keep (.s7 :: kRegs) s₀ t

theorem loop_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2))
    (hst : BS s B w n p iv (Divstep.invRunS 59 p iv x 0))
    (odd : p % 2 = 1) (hp0 : 0 < p) (hinv : (p * iv + 1) % 2 ^ 64 = 0)
    (pc : p < 2 ^ (64 * nu n)) (xc : x < 2 * 2 ^ (64 * nu n)) :
    WP isa (.loop batch (.nonzero .s7)) s (LoopAt s B Z w N n p iv x (3 * nu n + 2)) := by
  have hn := h.nuw
  have hw := h.ws.wle
  refine count_loop (by omega) (LoopAt s B Z w N n p iv x) (fun k hk t ⟨Ht, t7, It, Kt, kt⟩ => ?_)
    ⟨h, by simpa using h7, hst, Keys.Frame.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, ha, hb⟩ := run_bounds (k := k) odd hinv pc xc
  rw [show 3 * nu n + 2 - k = (3 * nu n + 2 - k - 1) + 1 by omega] at t7
  refine WP.mono (batch_ok Ht t7 It hN (by push_cast at bd ⊢; omega) fo fb gb ha hb hp0 pc hinv)
    fun u ⟨Hu, Iu, u7, Ku, ku⟩ => ?_
  refine ⟨⟨Hu, by rw [u7]; congr 1, Iu, Kt.trans Ku, Keep.trans' kt ku⟩, ?_⟩
  rw [u7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- After `k` batches of `f` and `g`. -/
def LoopG (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2 - k) ∧
    BG t B w n (Divstep.invRunS 59 p iv x k) ∧
    Keys.Frame B w [aF, aG, aT1, aT2, aW] [] s₀.mem t.mem ∧ Keep (.s7 :: kRegs) s₀ t

theorem loopG_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2))
    (hst : BG s B w n (Divstep.invRunS 59 p iv x 0))
    (odd : p % 2 = 1) (hinv : (p * iv + 1) % 2 ^ 64 = 0)
    (pc : p < 2 ^ (64 * nu n)) (xc : x < 2 * 2 ^ (64 * nu n)) :
    WP isa (.loop batchG (.nonzero .s7)) s (LoopG s B Z w N n p iv x (3 * nu n + 2)) := by
  have hn := h.nuw
  have hw := h.ws.wle
  refine count_loop (by omega) (LoopG s B Z w N n p iv x) (fun k hk t ⟨Ht, t7, It, Kt, kt⟩ => ?_)
    ⟨h, by simpa using h7, hst, Keys.Frame.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, -, -⟩ := run_bounds (k := k) odd hinv pc xc
  rw [show 3 * nu n + 2 - k = (3 * nu n + 2 - k - 1) + 1 by omega] at t7
  refine WP.mono (batchG_ok (p := p) (iv := iv) Ht t7 It hN (by push_cast at bd ⊢; omega) fo fb gb)
    fun u ⟨Hu, Iu, u7, Ku, ku⟩ => ?_
  refine ⟨⟨Hu, by rw [u7]; congr 1, Iu, Kt.trans Ku, Keep.trans' kt ku⟩, ?_⟩
  rw [u7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: the end

`normalize_ok`: `a` into `[0, p)`, negated if `f < 0`; `doublings_ok`:
`a 2^(5 (3 ν + 2)) mod p`; `finishG_ok`, `finishY_ok`: `|f|` and `a` into
arrays 1 and 3, `w` words each.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.RISCV64.Loops (Ahead)
open VG.RISCV64.RegUpd

/-- A number of `k + 1` words in two's complement, in `[-2^(64 k), 2^(64 k + 1))`:
its words, and its sign the top word's bit 63. -/
theorem sign_word {m : Mem} {B : Addr} {d k : Nat} {a : Int}
    (h : (wordsVal m B d (k + 1) : Int) % 2 ^ (64 * (k + 1)) = a % 2 ^ (64 * (k + 1)))
    (h1 : -(2 ^ (64 * k) : Int) ≤ a) (h2 : a < 2 * 2 ^ (64 * k)) :
    ((wordsVal m B d (k + 1) : Int) = if a < 0 then a + 2 ^ (64 * (k + 1)) else a) ∧
      (2 ^ 63 ≤ (word m B (d + 8 * k)).toNat ↔ a < 0) := by
  have hW := wordsVal_lt m B d (k + 1)
  have hQ : (2 : Int) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by rw [Nat.mul_succ, Int.pow_add]
  have hA : (0 : Int) < 2 ^ (64 * k) := by exact_mod_cast Nat.two_pow_pos _
  have hWQ : (wordsVal m B d (k + 1) : Int) < 2 ^ (64 * (k + 1)) := by exact_mod_cast hW
  have e1 : (wordsVal m B d (k + 1) : Int) = if a < 0 then a + 2 ^ (64 * (k + 1)) else a := by
    rw [← Int.emod_eq_of_lt (Int.natCast_nonneg _) hWQ, h]
    split
    · rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by rw [hQ]; nlinarith) (by omega)
    · exact Int.emod_eq_of_lt (by omega) (by rw [hQ]; nlinarith)
  refine ⟨e1, ?_⟩
  rw [← half_top _ (wordsVal_lt m B d k), ← wordsVal_succ_top]
  have e2 : ((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) = 2 ^ (64 * k) * 2 ^ 63 := by push_cast; rfl
  constructor
  · intro hle
    have hle' : ((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) ≤ wordsVal m B d (k + 1) := by exact_mod_cast hle
    rw [e2, e1] at hle'
    split at hle'
    · assumption
    · nlinarith
  · intro hneg
    have : ((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) ≤ wordsVal m B d (k + 1) := by
      rw [e2, e1, ite_eq_left hneg, hQ]; nlinarith
    exact_mod_cast this

/-- The arithmetic of `normalize`: `a + p` if `a < 0` (`V₁`), less `p` if no
borrow (`V₂`), `p - V₂` if `f < 0` (`V₃`), less `p` if no borrow (`V₄`). -/
theorem norm_end {p : Nat} {a : Int} {V1 V2 V3 V4 : Nat} (fneg : Prop) [Decidable fneg] (ha1 : -(p : Int) < a)
    (ha2 : a < 2 * p) (h1 : (V1 : Int) = if a < 0 then a + p else a) (h2 : V2 = if p ≤ V1 then V1 - p else V1)
    (h3 : V3 = if fneg then p - V2 else V2) (h4 : V4 = if p ≤ V3 then V3 - p else V3) :
    V4 < p ∧ (V4 : Int) ≡ (if fneg then -1 else 1) * a [ZMOD p] := by
  have key : V4 < p ∧ ∃ k : Int, (V4 : Int) = (if fneg then -1 else 1) * a + p * k := by
    subst h2 h3 h4
    split_ifs at h1 ⊢ <;> first
      | exact ⟨by omega, 0, by omega⟩ | exact ⟨by omega, 1, by omega⟩ | exact ⟨by omega, -1, by omega⟩
      | exact ⟨by omega, 2, by omega⟩
  obtain ⟨hlt, k, hk⟩ := key
  refine ⟨hlt, ?_⟩
  show (V4 : Int) % p = _ % p
  rw [hk, Int.add_mul_emod_self_left]

/-- The value of a sum less its carry out. -/
theorem carry_val {T V Q c : Nat} (hT : T < Q) (h : T + Q * c = V) : T = V % Q := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hT]

/-- `normalize`: `a` (`(-p, 2p)`, two's complement) into `[0, p)`, negated
modulo `p` if `f < 0`. -/
theorem normalize_ok {s : State} {B : Addr} {Z w N n p : Nat} {a f : Int} (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p) (hpA : p < 2 ^ (64 * nu n))
    (ha : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = a % 2 ^ (64 * (nu n + 1)))
    (ha1 : -(p : Int) < a) (ha2 : a < 2 * p)
    (hf : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = f % 2 ^ (64 * (nu n + 1)))
    (hf1 : -(p : Int) ≤ f) (hf2 : f ≤ p) :
    WP isa normalize s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aA, aT3, aT1] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w aA) (nu n + 1) < p ∧
      (wordsVal t.mem B (arr w aA) (nu n + 1) : Int) ≡ (if 0 ≤ f then 1 else -1) * a [ZMOD p] ∧
      Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  have := arr_al w aT3
  have := arr_al w aMz
  have := arr_al w aA
  have f3 := fitZ _ n3
  have fM := fitZ _ nM
  have fA := fitZ _ nA
  have hAp : (p : Int) < 2 ^ (64 * nu n) := by exact_mod_cast hpA
  obtain ⟨vA, sA⟩ := sign_word ha (by omega) (by omega)
  obtain ⟨-, sF⟩ := sign_word hf (by omega) (by omega)
  have hQA : 2 ^ (64 * (nu n + 1)) = 2 ^ (64 * nu n) * 2 ^ 64 := pow_succ64 _
  have hQ2 : 2 * 2 ^ (64 * nu n) ≤ 2 ^ (64 * (nu n + 1)) := by rw [hQA]; omega
  have hQI : ((2 ^ (64 * (nu n + 1)) : Nat) : Int) = 2 ^ (64 * (nu n + 1)) := by push_cast; rfl
  simp only [normalize, VG.Impl.Rsa.RISCV64.InvBatch.reduce, seqs]
  -- `a5 := 1`.
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (WP.keep [.a5] (Q := fun u => u.gpr .a5 = 1#64 ∧ u.mem = s.mem) (by brun [exec_li]; try rfl)
    (by rfl) (by rfl)) fun t1 ⟨⟨r5, m1⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  -- `[aT3] = a + p`.
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h1 (fun u hu => cntN1_ok hu) (K := nu n + 1) (by omega) (by omega) n3 nA nM hN)
    fun t2 ⟨h2, K2, v2, _, _, _, _, k2⟩ => ?_
  rw [m1, r5, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul, hp] at v2
  rw [m1] at K2
  have T2 := carry_val (wordsVal_lt _ _ _ _) v2
  -- `[aA] = a < 0 ? a + p : a`.
  rw [WP.seq_iff]
  refine WP.mono (signSel_ok h2 nA nA nA n3 hN (by decide)) fun t3 ⟨h3, K3, v3, _, k3⟩ => ?_
  have wt2 : word t2.mem B (arr w aA + 8 * nu n) = word s.mem B (arr w aA + 8 * nu n) :=
    keep_word K2 (o := 8 * nu n) (b := 64) (by omega) (by decide) (by simp) (fit _ nA)
  rw [keep_wv K2 hk (by decide) (fit _ nA), T2, wt2] at v3
  -- `[aA] = a mod p`.
  refine WP.mono (csub_ok (p := p) h3 nA nA n1 hN (by decide) (by decide) (by decide)
    (by rw [keep_wv K3 hk (by decide) (fit _ nM), keep_wv K2 hk (by decide) (fit _ nM), hp]) v3)
    fun t4 ⟨h4, K4, v4, k4⟩ => ?_
  have K34 : Keys.Frame B w [aA, aT1] [] t3.mem t4.mem := K4
  -- `[aT3] = p - a`.
  rw [WP.seq_iff]
  refine WP.mono (setup_ok h4 (fun t ht => cntN1_ok ht) (by decide) (by decide) (by decide))
    fun t5 ⟨h5, m5, p0, p1, p2, p3, p4, k5⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (Loops.subLoop_ok h5.ws.scr p0 p1 p2 p3 (by rw [p4]; decide) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k (by decide) (by omega)) (ahead_k (by decide) (by omega)))
    fun t6 ⟨b6, v6, out6, k6⟩ => ?_
  rw [m5, p4, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
    keep_wv K4 hk (by decide) (fit _ nM), keep_wv K3 hk (by decide) (fit _ nM), keep_wv K2 hk (by decide) (fit _ nM),
    hp] at v6
  rw [m5] at out6
  have K6 : Keys.Frame B w [aT3] [] t4.mem t6.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out6) (by omega) (by simp)
  have h6 := h5.of_keep (k6.mono (by decide))
  -- `[aA] = f < 0 ? p - a : a`.
  rw [WP.seq_iff]
  refine WP.mono (signSel_ok h6 nF nA nA n3 hN (by decide)) fun t7 ⟨h7, K7, v7, _, k7⟩ => ?_
  have K26 : Keys.Frame B w [aT3, aA, aT1] [] s.mem t6.mem :=
    ((K2.mono (by simp)).trans (K3.mono (by simp))).trans ((K34.mono (by simp)).trans (K6.mono (by simp)))
  have wF : word t6.mem B (arr w aF + 8 * nu n) = word s.mem B (arr w aF + 8 * nu n) :=
    keep_word K26 (o := 8 * nu n) (b := 64) (by omega) (by decide) (by simp) (fit _ nF)
  rw [wF, keep_wv K6 hk (by decide) (fit _ nA)] at v7
  refine WP.mono (csub_ok (p := p) h7 nA nA n1 hN (by decide) (by decide) (by decide)
    (by rw [keep_wv K7 hk (by decide) (fit _ nM), keep_wv K26 hk (by decide) (fit _ nM), hp]) v7)
    fun t8 ⟨h8, K8, v8, k8⟩ => ?_
  have k : Keep kRegs s t8 := Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans'
    (k1.mono (by decide)) k2) k3) k4) (k5.mono (by decide))) (k6.mono (by decide))) (Keep.trans' k7 k8)
  refine ⟨h8, (K26.mono (by simp)).trans ((K7.mono (by simp)).trans (K8.mono (by simp))), ?_⟩
  -- The arithmetic.
  have hQp : p + 2 * 2 ^ (64 * nu n) ≤ 2 ^ (64 * (nu n + 1)) := by rw [hQA]; omega
  have h1 : ((if 2 ^ 63 ≤ (word s.mem B (arr w aA + 8 * nu n)).toNat then
      (wordsVal s.mem B (arr w aA) (nu n + 1) + p) % 2 ^ (64 * (nu n + 1))
      else wordsVal s.mem B (arr w aA) (nu n + 1) : Nat) : Int) = if a < 0 then a + p else a := by
    by_cases hneg : a < 0
    · rw [ite_eq_left (sA.mpr hneg), ite_eq_left hneg]
      rw [ite_eq_left hneg, ← hQI] at vA
      have e : wordsVal s.mem B (arr w aA) (nu n + 1) + p = (a + p).toNat + 2 ^ (64 * (nu n + 1)) := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [ite_eq_right (fun h => hneg (sA.mp h)), ite_eq_right hneg]
      rw [ite_eq_right hneg] at vA
      exact vA
  have hV1 : (if 2 ^ 63 ≤ (word s.mem B (arr w aA + 8 * nu n)).toNat then
      (wordsVal s.mem B (arr w aA) (nu n + 1) + p) % 2 ^ (64 * (nu n + 1))
      else wordsVal s.mem B (arr w aA) (nu n + 1)) < 2 * p := by
    have := h1; split at this <;> omega
  generalize (if 2 ^ 63 ≤ (word s.mem B (arr w aA + 8 * nu n)).toNat then
      (wordsVal s.mem B (arr w aA) (nu n + 1) + p) % 2 ^ (64 * (nu n + 1))
      else wordsVal s.mem B (arr w aA) (nu n + 1)) = V1 at h1 hV1 v4
  have hV2 : wordsVal t4.mem B (arr w aA) (nu n + 1) < p := by rw [v4]; split <;> omega
  have T6 : wordsVal t6.mem B (arr w aT3) (nu n + 1) = p - wordsVal t4.mem B (arr w aA) (nu n + 1) := by
    have hR := wordsVal_lt t6.mem B (arr w aT3) (nu n + 1)
    generalize 2 ^ (64 * (nu n + 1)) = R at hR v6 hQp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b6 with e | e <;> rw [e] at v6 <;> omega
  rw [T6] at v8
  obtain ⟨r1, r2⟩ := norm_end (2 ^ 63 ≤ (word s.mem B (arr w aF + 8 * nu n)).toNat) ha1 ha2 h1 v4 rfl v8
  refine ⟨r1, ?_, k⟩
  have e : (if 2 ^ 63 ≤ (word s.mem B (arr w aF + 8 * nu n)).toNat then (-1 : Int) else 1) =
      if 0 ≤ f then 1 else -1 := by
    by_cases hf0 : 0 ≤ f
    · rw [ite_eq_right (fun h => absurd (sF.mp h) (by omega)), ite_eq_left hf0]
    · rw [ite_eq_left (sF.mpr (by omega)), ite_eq_right hf0]
  rw [← e]; exact r2

/-- `double`: `[a] = 2 a mod p`, for `a < p`. -/
theorem double_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p) (ha : wordsVal s.mem B (arr w aA) (nu n + 1) = a)
    (hap : a < p) (hpA : p < 2 ^ (64 * nu n)) :
    WP isa double s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aA, aT3, aT1] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w aA) (nu n + 1) = (2 * a) % p ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have n1 : aT1 < N := by unfold aT1; omega
  rw [double]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (WP.keep [.a5] (Q := fun u => u.gpr .a5 = 1#64 ∧ u.mem = s.mem) (by brun [exec_li]; try rfl)
    (by rfl) (by rfl)) fun t1 ⟨⟨r5, m1⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h1 (fun u hu => cntN1_ok hu) (K := nu n + 1) (by omega) (by omega) n3 nA nA hN)
    fun t2 ⟨h2, K2, v2, _, _, _, _, k2⟩ => ?_
  rw [m1, ha, r5, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul] at v2
  have hR : 2 * a < 2 ^ (64 * (nu n + 1)) := by rw [pow_succ64]; omega
  have v2' : wordsVal t2.mem B (arr w aT3) (nu n + 1) = 2 * a := by
    rw [carry_val (wordsVal_lt _ _ _ _) v2, show a + a = 2 * a by omega, Nat.mod_eq_of_lt hR]
  rw [m1] at K2
  refine WP.mono (csub_ok (p := p) h2 nA n3 n1 hN (by decide) (by decide) (by decide)
    (by rw [keep_wv K2 (by omega) (by decide) (fit _ nM), hp]) v2') fun t3 ⟨h3, K3, v3, k3⟩ => ?_
  refine ⟨h3, (K2.mono (by simp)).trans (K3.mono (by simp)), ?_,
    Keep.trans' (Keep.trans' (k1.mono (by decide)) k2) k3⟩
  rw [v3]
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- After `k` doublings. -/
def DoubleAt (s₀ : State) (B : Addr) (Z w N n p a₀ : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (5 * (3 * nu n + 2) - k) ∧
    wordsVal t.mem B (arr w aA) (nu n + 1) = Rsa.Divstep.doubled p a₀ k ∧
    Keys.Frame B w [aA, aT3, aT1] [] s₀.mem t.mem ∧ Keep (.s7 :: kRegs) s₀ t

theorem shl4 {k : Nat} (h : 16 * k < 2 ^ 64) : BitVec.ofNat 64 k <<< 4 = BitVec.ofNat 64 (16 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `doublings`: `[a] = a 2^(5 (3 ν + 2)) mod p`. -/
theorem doublings_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p) (ha : wordsVal s.mem B (arr w aA) (nu n + 1) = a)
    (hap : a < p) (hpA : p < 2 ^ (64 * nu n)) :
    WP isa doublings s (DoubleAt s B Z w N n p a (5 * (3 * nu n + 2))) := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nM : aMz < N := by unfold aMz; omega
  rw [doublings, WP.seq_iff]
  refine WP.mono (WP.keep [.t3, .s7] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 (5 * (3 * nu n + 2)) ∧
    u.mem = s.mem) ?_ (by rfl) (by rfl)) fun t0 ⟨⟨r7, m0⟩, k0⟩ => ?_
  · brun [cntN, h.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega), shl4 (show 16 * nu n < 2 ^ 64 by omega)]
    have : nu n = (n + 1) / 2 := rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, show (10#64).toNat = 10 from rfl]
    omega
  have h0 : Ctx t0 B Z w N n := h.of_keep7 (k0.mono (by decide))
  refine count_loop (by omega) (DoubleAt s B Z w N n p a) (fun k hk t ⟨Ht, t7, vt, Kt, kt⟩ => ?_)
    ⟨h0, by simpa using r7, by rw [m0, ha, Rsa.Divstep.doubled_zero hap], by rw [m0]; exact Keys.Frame.refl _ _ _ _ _,
      k0.mono (by decide)⟩
  have pt : wordsVal t.mem B (arr w aMz) (nu n + 1) = p := by
    rw [keep_wv Kt (by omega) (by decide) (fit _ nM), hp]
  rw [WP.seq_iff]
  refine WP.mono (double_ok Ht hN pt vt (Rsa.Divstep.doubled_lt (by omega)) hpA) fun u ⟨Hu, Ku, vu, ku⟩ => ?_
  rw [show 5 * (3 * nu n + 2) - k = (5 * (3 * nu n + 2) - k - 1) + 1 by omega] at t7
  have u7 : u.gpr .s7 = BitVec.ofNat 64 (5 * (3 * nu n + 2) - k - 1 + 1) := (ku.gpr (by decide)).trans t7
  refine WP.mono (dec_ok u7) fun y ⟨⟨y7, ym⟩, ky⟩ => ?_
  refine ⟨⟨Hu.of_keep7 (ky.mono (by decide)), by rw [y7]; congr 1, by rw [ym, vu, Rsa.Divstep.doubled_next],
    Kt.trans (by rw [ym]; exact Ku), Keep.trans' kt (Keep.trans' (ku.mono (by decide)) (ky.mono (by decide)))⟩, ?_⟩
  rw [y7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The end -/

/-- The words of a number that is zero. -/
theorem words_zero {m : Mem} {B : Addr} {d : Nat} : ∀ {k : Nat}, wordsVal m B d k = 0 →
    ∀ i < k, word m B (d + 8 * i) = 0
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, h, i, hi => by
    rw [wordsVal_succ_top] at h
    have hp := Nat.two_pow_pos (64 * k)
    have h1 : wordsVal m B d k = 0 := by omega
    have h2 : (word m B (d + 8 * k)).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (word m B (d + 8 * k)).toNat with e | e
      · exact e
      · have := Nat.mul_pos hp e; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact words_zero h1 i hi
    · exact BitVec.eq_of_toNat_eq h2

/-- `k` words, then zero words to `k + j`. -/
theorem wv_extend {m : Mem} {B : Addr} {d k : Nat} : ∀ j, (∀ i, k ≤ i → i < k + j → word m B (d + 8 * i) = 0) →
    wordsVal m B d (k + j) = wordsVal m B d k
  | 0, _ => rfl
  | j + 1, h => by
    rw [← Nat.add_assoc, wordsVal_succ_top, h (k + j) (by omega) (by omega), wv_extend j (fun i h1 h2 => h i h1 (by omega))]
    rfl

/-- `k ≤ W + 1` words holding `v < 2^(64 W)`, the words after them zero to word
`W`: the `W` words are `v`. -/
theorem wv_num {m : Mem} {B : Addr} {d k W v : Nat} (hk : k ≤ W + 1) (hv : wordsVal m B d k = v)
    (hz : ∀ i, k ≤ i → i < W → word m B (d + 8 * i) = 0) (hvW : v < 2 ^ (64 * W)) : wordsVal m B d W = v := by
  by_cases hkW : k ≤ W
  · have e := wv_extend (m := m) (B := B) (d := d) (k := k) (W - k) (fun i h1 h2 => hz i h1 (by omega))
    rw [show k + (W - k) = W by omega] at e
    rw [e, hv]
  · obtain rfl : k = W + 1 := by omega
    rw [wordsVal_succ_top] at hv
    have hl := wordsVal_lt m B d W
    rcases Nat.eq_zero_or_pos (word m B (d + 8 * W)).toNat with e | e
    · rw [e, Nat.mul_zero, Nat.add_zero] at hv; exact hv
    · have : 2 ^ (64 * W) ≤ 2 ^ (64 * W) * (word m B (d + 8 * W)).toNat := Nat.le_mul_of_pos_right _ e
      omega

/-- `finishG`: `[1] = |f|`, `w` words. -/
theorem finishG_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {f : Int}
    (hf : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = f % 2 ^ (64 * (nu n + 1)))
    (hfr : f.natAbs < 2 ^ (64 * nu n)) :
    WP isa finishG s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aGcd, aT1] [] s.mem t.mem ∧
      num t.mem B w aGcd = f.natAbs ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nG : aGcd < N := by unfold aGcd; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have fG := fitZ _ nG
  have fF := fitZ _ nF
  have f1 := fitZ _ n1
  have := arr_al w aGcd
  have := arr_al w aF
  have := arr_al w aT1
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have hnw' := h.ws.nowrap
  have habs : ((f.natAbs : Nat) : Int) = if f < 0 then -f else f := by
    split
    · exact Int.ofNat_natAbs_of_nonpos (by omega)
    · exact Int.natAbs_of_nonneg (by omega)
  have hfr' : ((f.natAbs : Nat) : Int) < 2 ^ (64 * nu n) := by exact_mod_cast hfr
  obtain ⟨vF, sF⟩ := sign_word hf (by split at habs <;> omega) (by split at habs <;> omega)
  have hQA : 2 ^ (64 * (nu n + 1)) = 2 ^ (64 * nu n) * 2 ^ 64 := pow_succ64 _
  have hQI : ((2 ^ (64 * (nu n + 1)) : Nat) : Int) = 2 ^ (64 * (nu n + 1)) := by push_cast; rfl
  rw [finishG]; simp only [seqs]; rw [WP.seq_iff]
  -- `[1] = 0`.
  refine WP.mono (zeroW_ok h nG hN) fun t1 ⟨h1, K1, out1, z1, k1⟩ => ?_
  have zw := words_zero z1
  rw [WP.seq_iff]
  refine WP.mono (setup_ok h1 (fun t ht => cntN1_ok ht) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, m2, p0, p1, p2, p3, p4, k2⟩ => ?_
  rw [WP.seq_iff]
  -- `[aT1] = -f`.
  refine WP.mono (Loops.subLoop_ok h2.ws.scr p0 p1 p2 p3 (by rw [p4]; decide) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k (by decide) (by omega)) (ahead_k (by decide) (by omega)))
    fun t3 ⟨b3, v3, out3, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have zG : wordsVal t1.mem B (arr w aGcd) (nu n + 1) = 0 :=
    VG.Proof.Bignum.RISCV64.wordsVal_zero (fun i hi => zw i (by omega))
  rw [m2, p4, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, zG,
    keep_wv K1 hk1 (by decide) (fit _ nF)] at v3
  rw [m2] at out3
  have K3 : Keys.Frame B w [aT1] [] t1.mem t3.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out3) (by omega) (by simp)
  refine WP.mono (signSel_ok h3 nF nG nF n1 hN (by decide)) fun t4 ⟨h4, K4, v4, out4, k4⟩ => ?_
  have K13 : Keys.Frame B w [aGcd, aT1] [] s.mem t3.mem := (K1.mono (by simp)).trans (K3.mono (by simp))
  have wF : word t3.mem B (arr w aF + 8 * nu n) = word s.mem B (arr w aF + 8 * nu n) :=
    keep_word K13 (o := 8 * nu n) (b := 64) (by omega) (by decide) (by simp) (fit _ nF)
  rw [wF, keep_wv K13 hk1 (by decide) (fit _ nF)] at v4
  have gcd1 : wordsVal t4.mem B (arr w aGcd) (nu n + 1) = f.natAbs := by
    rw [v4]
    have hR := wordsVal_lt t3.mem B (arr w aT1) (nu n + 1)
    by_cases hneg : f < 0
    · rw [ite_eq_left (sF.mpr hneg)]
      rw [ite_eq_left hneg] at vF habs
      have hQA' : (2 : Int) ^ (64 * nu n) < 2 ^ (64 * (nu n + 1)) := by
        exact_mod_cast Nat.pow_lt_pow_right (by decide) (by omega)
      have hFpos : 0 < wordsVal s.mem B (arr w aF) (nu n + 1) := by omega
      rw [← hQI] at vF
      generalize 2 ^ (64 * (nu n + 1)) = R at hR v3 vF
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b3 with b | b <;> rw [b] at v3 <;> omega
    · rw [ite_eq_right (fun h => hneg (sF.mp h))]
      rw [ite_eq_right hneg] at vF habs
      omega
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' k1 (k2.mono (by decide)))
    (k3.mono (by decide))) k4
  refine ⟨h4, K13.trans (K4.mono (by simp)), ?_, k⟩
  show wordsVal t4.mem B (arr w aGcd) w = _
  have hnw : 2 ^ (64 * nu n) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  refine wv_num (k := nu n + 1) (by omega) gcd1 (fun i hi1 hi2 => ?_) (by omega)
  rw [out4.word (d := arr w aGcd + 8 * i) (by omega) (by omega),
    out3.word (d := arr w aGcd + 8 * i) (by have := arr_disj (w := w) (show aGcd ≠ aT1 by decide); omega)
    (by omega)]
  exact zw i (by omega)

/-- `finishY`: `[3] = y`, `w` words. -/
theorem finishY_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {y : Nat}
    (hy : wordsVal s.mem B (arr w aA) (nu n + 1) = y) (hyr : y < 2 ^ (64 * w)) :
    WP isa finishY s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aY] [] s.mem t.mem ∧
      num t.mem B w aY = y ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nY : aY < N := by unfold aY; omega
  have nA : aA < N := by unfold aA; omega
  have fY := fitZ _ nY
  have fA := fitZ _ nA
  have := arr_al w aY
  have := arr_al w aA
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have hnw' := h.ws.nowrap
  rw [finishY]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (zeroW_ok h nY hN) fun t5 ⟨h5, K5, out5, z5, k5⟩ => ?_
  have zw := words_zero z5
  rw [WP.seq_iff]
  have hb6 : WP isa (.block (ptr .t0 aY ++ ptr .t1 aA ++ cntN1)) t5 fun u => Ctx u B Z w N n ∧ u.mem = t5.mem ∧
      u.gpr .t0 = off B (arr w aY) ∧ u.gpr .t1 = off B (arr w aA) ∧ u.gpr .t3 = BitVec.ofNat 64 (nu n + 1) ∧
      Keep kRegs t5 u := by
    refine ptr2_ok h5.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) fun t p0 p1 kt mt => ?_
    have ht := h5.of_keep (kt.mono (by decide))
    refine WP.mono (cntN1_ok ht) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
    have k0 : Keep kRegs t5 x := (kt.trans kx).mono (by decide)
    refine ⟨h5.of_keep k0, xm.trans mt, ?_, ?_, x3, k0⟩
    · rw [kx.gpr (by decide)]; exact p0
    · rw [kx.gpr (by decide)]; exact p1
  refine WP.mono hb6 fun t6 ⟨h6, m6, q0, q1, q3, k6⟩ => ?_
  refine WP.mono (Loops.copyLoop_ok h6.ws.scr q0 q1 q3 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (ahead_k (by decide) (by omega))) fun t7 ⟨v7, out7, k7⟩ => ?_
  rw [m6] at v7 out7
  have K57 : Keys.Frame B w [aY] [] s.mem t7.mem := K5.trans
    (Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out7) (by omega) (by simp))
  have yA : wordsVal t5.mem B (arr w aA) (nu n + 1) = y := by
    rw [keep_wv K5 hk1 (by decide) (fit _ nA), hy]
  have k : Keep kRegs s t7 := Keep.trans' (Keep.trans' k5 k6) (k7.mono (by decide))
  refine ⟨h.of_keep k, K57, ?_, k⟩
  show wordsVal t7.mem B (arr w aY) w = _
  refine wv_num (k := nu n + 1) (by omega) (by rw [v7, yA]) (fun i hi1 hi2 => ?_) hyr
  rw [out7.word (d := arr w aY + 8 * i) (by omega) (by omega)]
  exact zw i (by omega)

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: the start

`init_ok`: from `x` in array 0 and the odd `m` in array 8, both below
`2^(32 n)`, the start of the inversion modulo `m` (`Divstep.invRunS 59`'s
state 0): `f = m`, `g = oddInput m x`, `a = 0`, `b = 1`, `d = 1`, with
`-m⁻¹ mod 2^64` in the window and `3 ν + 2` batches to run.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.RISCV64.Loops (Ahead)
open VG.RISCV64.RegUpd
open VG.Proof.Rsa.Divstep (oddInput)

/-- `ptr r j` alone, run. -/
theorem runBlock_ptr_nil (B : Addr) (w : Nat) {s : State} {r : Reg} {j : Nat}
    (h10 : s.gpr .s10 = BitVec.ofNat 64 (S w)) (h11 : s.gpr .s11 = B) (hr10 : r ≠ .s10) (hr11 : r ≠ .s11)
    (hj : j < 2048) : runBlock isa (ptr r j) s = some (s.write r (off B (arr w j))) := by
  have := runBlock_ptr B w (s := s) (r := r) (j := j) [] h10 h11 hr10 hr11 hj
  rw [List.append_nil] at this
  rw [this, runBlock_nil]

/-- The first `k` words of `k + j` words holding `v < 2^(64 k)`. -/
theorem wv_trunc {m : Mem} {B : Addr} {d k : Nat} : ∀ {j v : Nat}, wordsVal m B d (k + j) = v →
    v < 2 ^ (64 * k) → wordsVal m B d k = v
  | 0, _, h, _ => h
  | j + 1, v, h, hv => by
    rw [← Nat.add_assoc, wordsVal_succ_top] at h
    have hk : 2 ^ (64 * k) ≤ 2 ^ (64 * (k + j)) := Nat.pow_le_pow_right (by decide) (by omega)
    have hl := wordsVal_lt m B d (k + j)
    have e : wordsVal m B d (k + j) = v := by
      rcases Nat.eq_zero_or_pos (word m B (d + 8 * (k + j))).toNat with e | e
      · rw [e, Nat.mul_zero, Nat.add_zero] at h; exact h
      · have : 2 ^ (64 * (k + j)) ≤ 2 ^ (64 * (k + j)) * (word m B (d + 8 * (k + j))).toNat :=
          Nat.le_mul_of_pos_right _ e
        omega
    exact wv_trunc e hv

/-- The low `k ≤ W` words of `W` words holding `v < 2^(64 k)`. -/
theorem wv_low {m : Mem} {B : Addr} {d W k v : Nat} (hk : k ≤ W) (hv : wordsVal m B d W = v)
    (hvk : v < 2 ^ (64 * k)) : wordsVal m B d k = v :=
  wv_trunc (j := W - k) (by rw [show k + (W - k) = W by omega]; exact hv) hvk

/-- `initA`: `[2] = m`, `ν` words and a zero word `ν`. -/
theorem initA_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {m : Nat}
    (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n)) :
    WP isa initA s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aMz] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w aMz) (nu n) = m ∧ wordsVal t.mem B (arr w aMz) (nu n + 1) = m ∧
      Keep kRegs s t := by
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := h.nuw
  have := h.nu1
  have := h.nw
  have := h.wbig
  have hnw' := h.ws.nowrap
  have room := h.room
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nI : aMin < N := by unfold aMin; omega
  have fM := fitZ _ nM
  have fI := fitZ _ nI
  have := arr_al w aMz
  have := arr_al w aMin
  have hmν : m < 2 ^ (64 * nu n) := Nat.lt_of_lt_of_le hmn (pow_nu n)
  simp only [initA, seqs]
  -- `[2] = m`, `ν` words.
  rw [WP.seq_iff, WP.seq_iff]
  refine ptr2_ok h.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u p0 p1 ku mu => ?_
  refine WP.mono (cntN_ok (h.of_keep (ku.mono (by decide)))) fun u' ⟨⟨u3, um'⟩, ku'⟩ => ?_
  have k1a : Keep kRegs s u' := (ku.trans ku').mono (by decide)
  refine WP.mono (Loops.copyLoop_ok (dO := arr w aMz) (dA := arr w aMin) (h.of_keep k1a).ws.scr
    (by rw [ku'.gpr (by decide)]; exact p0) (by rw [ku'.gpr (by decide)]; exact p1) u3 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (ahead_k (by decide) (by omega)))
    fun t1 ⟨v1, out1, kt1⟩ => ?_
  rw [um', mu] at v1 out1
  have k1 : Keep kRegs s t1 := Keep.trans' k1a (kt1.mono (by decide))
  have h1 := h.of_keep k1
  rw [wv_low (k := nu n) (by omega) hm hmν] at v1
  -- Its word `ν` zero.
  refine WP.mono (WP.keep [.t1, .t3, .t5] (Q := fun u => u.mem = t1.mem.writeW (off B (arr w aMz + 8 * nu n))
      (0 : BitVec 64)) ?_ (by rfl) (by rfl)) fun t2 ⟨m2, k2⟩ => ?_
  · brun [exec_li, topOf, cntN, List.append_assoc, runBlock_ptr B w, (show aMz < 2048 by decide),
      h1.ws.s10, h1.ws.s11, h1.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega),
      ofNat_shl3 (show 8 * nu n < 2 ^ 64 by omega), off_add, fin64_exec_li_zero,
      h1.ws.scr.st (show arr w aMz + 8 * nu n + 8 ≤ Z by omega),
      h1.ws.scr.al8 (show arr w aMz + 8 * nu n + 8 ≤ Z by omega) (by omega)]
    try rfl
  have k : Keep kRegs s t2 := Keep.trans' k1 (k2.mono (by decide))
  have o2 := writeW_outside t1.mem B (d := arr w aMz + 8 * nu n) (0 : BitVec 64) (by omega)
  have v2 : wordsVal t2.mem B (arr w aMz) (nu n) = m := by
    rw [m2, o2.wordsVal (by omega) (by omega), v1]
  refine ⟨h.of_keep k, ?_, v2, ?_, k⟩
  · exact (Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out1) (by omega) (by simp)).trans
      (by rw [m2]; exact Keys.Frame.of_arr (d := 8 * nu n) o2 (by omega) (by simp))
  · rw [m2, fin64_wordsVal_write_top _ _ _ _ _ (by omega), v1]; rfl

theorem newton_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .t5).toNat : Int) * (t.gpr .t6).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      ((((t'.gpr .t5).toNat : Int) * (t'.gpr .t6).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
        t'.gpr .t5 = t.gpr .t5 ∧ t'.mem = t.mem) ∧ Keep [.t6, .a5, .t4] t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold newton
  brun [r2_exec_li_two]
  exact VG.Proof.Bignum.newton_step hj h (newton_val _ _)

/-- `-x mod 2⁶⁴` is an inverse of `-a` modulo `2^64` when `x` is one of `a`. -/
theorem neg_inv64 {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) :
    (a * ((2 ^ 64 - x % 2 ^ 64) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  generalize hy : (2 ^ 64 - x % 2 ^ 64) % 2 ^ 64 = y
  have hxy : (x + y) % 2 ^ 64 = 0 := by omega
  have h1 : (2 ^ 64 : Int) ∣ (a : Int) * x - 1 := Int.dvd_of_emod_eq_zero h
  have h2 : (2 ^ 64 : Int) ∣ ((x + y : Nat) : Int) :=
    Int.dvd_of_emod_eq_zero (show ((x + y : Nat) : Int) % (2 ^ 64 : Int) = 0 by omega)
  have h3 : (2 ^ 64 : Int) ∣ ((a * y + 1 : Nat) : Int) := by
    have e : ((a * y + 1 : Nat) : Int) = (a : Int) * ((x + y : Nat) : Int) - ((a : Int) * x - 1) := by
      push_cast; grind
    rw [e]
    exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h2) h1
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp (by exact_mod_cast h3))

/-- `initB`: `-m⁻¹ mod 2^64` into the window, from `m`'s low word. -/
theorem initB_ok {t7 : State} {B : Addr} {Z w N n : Nat} (h7 : Ctx t7 B Z w N n) {m : Nat}
    (pv : wordsVal t7.mem B (arr w aMz) (nu n + 1) = m) (hodd : m % 2 = 1) :
    WP isa initB t7 fun t9 => Ctx t9 B Z w N n ∧ Keys.Frame B w [aW] [] t7.mem t9.mem ∧
      (∃ iv, (m * iv + 1) % 2 ^ 64 = 0 ∧ (t9.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) ∧
      Keep kRegs t7 t9 := by
  have h := h7
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := h.nw
  have := h.wbig
  have hnw' := h.ws.nowrap
  have room := h.room
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nW : aW < N := by unfold aW; omega
  have fM := fitZ _ nM
  have fW := fitZ _ nW
  have aW8 := arr_al w aW
  have := arr_al w aMz
  have hs := h.ws.scr
  have d0p : (word t7.mem B (arr w aMz)).toNat % 2 ^ 64 = m % 2 ^ 64 := by
    have e : wordsVal t7.mem B (arr w aMz) (nu n + 1) =
        (word t7.mem B (arr w aMz)).toNat + 2 ^ 64 * wordsVal t7.mem B (arr w aMz + 8) (nu n) := rfl
    rw [pv] at e; omega
  have hd := (word t7.mem B (arr w aMz)).isLt
  rw [initB, show ptr .a4 aMz ++ ([.load .d .t5 .a4 0, mov .t6 .t5] : List Instr) ++ newton ++ newton ++ newton ++
      newton ++ newton ++ ([.li .a5 0, .sub .t1 .a5 .t6] : List Instr) ++ ptr .a4 aW ++
      ([.store .d .t1 .a4 wIv] : List Instr) =
    (ptr .a4 aMz ++ ([.load .d .t5 .a4 0, mov .t6 .t5] : List Instr)) ++ (newton ++ (newton ++ (newton ++ (newton ++
      (newton ++ (([.li .a5 0, .sub .t1 .a5 .t6] : List Instr) ++ ptr .a4 aW ++
        ([.store .d .t1 .a4 wIv] : List Instr))))))) by
    simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.a4, .t5, .t6] (Q := fun u => u.gpr .t5 = word t7.mem B (arr w aMz) ∧
      u.gpr .t6 = word t7.mem B (arr w aMz) ∧ u.mem = t7.mem) ?_ (by rfl) (by rfl))
    fun u0 ⟨⟨u5, u6, um⟩, k0⟩ => ?_
  · brun [exec_li, List.append_assoc, runBlock_ptr B w, runBlock_ptr_nil B w, (show aMz < 2048 by decide),
      h.ws.s10, h.ws.s11, mov, add_ofNat_zero', hs.ld (show arr w aMz + 8 ≤ Z by omega),
      hs.al8 (show arr w aMz + 8 ≤ Z by omega) (by omega)]
  have e₀ : (((u0.gpr .t5).toNat : Int) * (u0.gpr .t6).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [u5, u6]
    have h1 := VG.Proof.Bignum.odd_sq _ (show (word t7.mem B (arr w aMz)).toNat % 2 = 1 by omega)
    have h2 : (((word t7.mem B (arr w aMz)).toNat : Int) * (word t7.mem B (arr w aMz)).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((word t7.mem B (arr w aMz)).toNat : Int) * (word t7.mem B (arr w aMz)).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u0 (j := 3) (by decide) e₀) fun u1 ⟨⟨e₁, b₁, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u1 (j := 6) (by decide) e₁) fun u2 ⟨⟨e₂, b₂, m₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u2 (j := 12) (by decide) e₂) fun u3 ⟨⟨e₃, b₃, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u3 (j := 24) (by decide) e₃) fun u4 ⟨⟨e₄, b₄, m₄⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u4 (j := 32) (by decide) (VG.Proof.Bignum.emod_pow_weaken (show 32 ≤ 2 * 24 by decide) e₄))
    fun u5' ⟨⟨e₅, b₅, m₅⟩, k₅⟩ => ?_
  have k05 : Keep kRegs t7 u5' := (((((k0.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  have h5 := h.of_keep k05
  have m05 : u5'.mem = t7.mem := by rw [m₅, m₄, m₃, m₂, m₁, um]
  refine WP.mono (WP.keep [.a4, .a5, .t1] (Q := fun u => u.mem = u5'.mem.writeW (off B (arr w aW + 40))
      (BitVec.ofNat 64 0 - u5'.gpr .t6)) ?_ (by rfl) (by rfl)) fun t9 ⟨m9, k9⟩ => ?_
  · brun [exec_li, wIv, List.append_assoc, runBlock_ptr B w, (show aW < 2048 by decide), h5.ws.s10, h5.ws.s11,
      exec_store_d, fin64_exec_li_zero, h5.ws.scr.st (show arr w aW + 40 + 8 ≤ Z by omega),
      h5.ws.scr.al8 (show arr w aW + 40 + 8 ≤ Z by omega) (by omega)]
  have h9 := h5.of_keep (k9.mono (by decide))
  have o9 := writeW_outside u5'.mem B (d := arr w aW + 40) (BitVec.ofNat 64 0 - u5'.gpr .t6) (by omega)
  have b5 : u5'.gpr .t5 = word t7.mem B (arr w aMz) := by rw [b₅, b₄, b₃, b₂, b₁, u5]
  rw [b5] at e₅
  have F9 : Keys.Frame B w [aW] [] t7.mem t9.mem := by
    rw [m9, ← m05]; exact Keys.Frame.of_arr (o := aW) (d := 40) o9 (by omega) (by simp)
  refine ⟨h9, F9, ⟨(BitVec.ofNat 64 0 - u5'.gpr .t6).toNat, ?_, by rw [m9, show arr w aW + wIv = arr w aW + 40 from rfl, Mem.readW_writeW_self64]⟩,
    Keep.trans' k05 (k9.mono (by decide))⟩
  have nv := neg_inv64 e₅
  have e2 : (BitVec.ofNat 64 0 - u5'.gpr .t6).toNat = (2 ^ 64 - (u5'.gpr .t6).toNat % 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e2, Nat.add_mod, Nat.mul_mod, ← d0p, Nat.mod_mod]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at nv
  exact nv

/-- Bit 0 of a word, inverted. -/
theorem even_bit64 (x : BitVec 64) :
    ((x &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1).toNat = (if x.toNat % 2 = 0 then 1 else 0) := by
  rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e <;> rw [e] <;> rfl

/-- The registers `init` changes. -/
abbrev initRegs : List Reg := .s7 :: kRegs

/-- `[j] = 0`, `ν + 1` words (`.seq (ptr t0 j ++ cntN1) zeros`). -/
theorem zeroN_ok {s : State} {B : Addr} {Z w N n j : Nat} (h : Ctx s B Z w N n) (hj : j < N) (hN : N ≤ 256) :
    WP isa (.seq (.block (ptr .t0 j ++ cntN1)) zeros) s fun t => Ctx t B Z w N n ∧
      Keys.Frame B w [j] [] s.mem t.mem ∧ wordsVal t.mem B (arr w j) (nu n + 1) = 0 ∧ Keep kRegs s t := by
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  have fj := h.ws.arr_fit hj
  have := arr_al w j
  rw [WP.seq_iff]
  refine ptr_ok h.ws (by decide) (by decide) (by omega) ?_
  refine WP.mono (cntN1_ok (h.of_keep ((Keep.write _ .t0 _).mono (by decide)))) fun x ⟨⟨q3, xm⟩, kx⟩ => ?_
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun u => u.gpr .t5 = 0 ∧ u.mem = x.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y0, ym⟩, ky⟩ => ?_
  have ka : Keep kRegs s y := (((Keep.write _ .t0 _).trans kx).trans ky).mono (by decide)
  refine WP.mono (Loops.zeroLoop_ok (dO := arr w j) (n := nu n + 1) (h.of_keep ka).ws.scr
    (by rw [ky.gpr (by decide), kx.gpr (by decide)]; simp [gpr_write])
    (by rw [ky.gpr (by decide)]; exact q3) y0 (by omega) (by omega) (by omega) (by omega))
    fun t ⟨z, out, kt⟩ => ?_
  rw [ym, xm, mem_write] at out
  exact ⟨h.of_keep (Keep.trans' ka (kt.mono (by decide))),
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega) (by simp), z,
    Keep.trans' ka (kt.mono (by decide))⟩

/-- `initC`: `f = m`, `g = oddInput m x`, `(a, b) = (0, 1)`, `d = 1` and `3 ν + 2` batches. -/
theorem initC_ok {t9 : State} {B : Addr} {Z w N n : Nat} (h9 : Ctx t9 B Z w N n) (hN : N ≤ 256)
    {x m iv : Nat} (hx : wordsVal t9.mem B (arr w aX) (nu n) = x)
    (pv9 : wordsVal t9.mem B (arr w aMz) (nu n + 1) = m) (pv9' : wordsVal t9.mem B (arr w aMz) (nu n) = m)
    (hivw : (t9.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) :
    WP isa initC t9 fun t => Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2) ∧
      BS t B w n m iv (Divstep.invRunS 59 m iv (oddInput m x) 0) ∧
      Keys.Frame B w [aW, aF, aG, aA, aB] [] t9.mem t.mem ∧ Keep initRegs t9 t := by
  have hS : S w = 8 * (w + 2) := rfl
  have h := h9
  have := h.ws.wle
  have := h.nuw
  have := h.nu1
  have := h.nw
  have := h.wbig
  have hnw' := h.ws.nowrap
  have room := h.room
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nB : aB < N := by unfold aB; omega
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nX : aX < N := by unfold aX; omega
  have fM := fitZ _ nM
  have fB := fitZ _ nB
  have fW := fitZ _ nW
  have fF := fitZ _ nF
  have fG := fitZ _ nG
  have fX := fitZ _ nX
  have := arr_al w aMz
  have := arr_al w aB
  have := arr_al w aF
  have := arr_al w aG
  have := arr_al w aX
  have aW8 := arr_al w aW
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  simp only [initC, seqs]
  -- `f = m`.
  rw [WP.seq_iff, WP.seq_iff]
  refine ptr2_ok h9.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun x10 p0' p1'' kx mx => ?_
  refine WP.mono (cntN1_ok (h9.of_keep (kx.mono (by decide)))) fun x10' ⟨⟨q3'', xm⟩, kx'⟩ => ?_
  have k10a : Keep kRegs t9 x10' := (kx.trans kx').mono (by decide)
  have h10a := h9.of_keep k10a
  refine WP.mono (Loops.copyLoop_ok (dO := arr w aF) (dA := arr w aMz) h10a.ws.scr
    (by rw [kx'.gpr (by decide)]; exact p0') (by rw [kx'.gpr (by decide)]; exact p1'') q3''
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (ahead_k (by decide) (by omega)))
    fun t10 ⟨vF, out10, k10⟩ => ?_
  rw [xm, mx, pv9] at vF
  rw [xm, mx] at out10
  have h10 := h10a.of_keep (k10.mono (by decide))
  have a10 : Keys.Frame B w [aF] [] t9.mem t10.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by omega) (by simp)
  -- `k = 1` for an even `x`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.t0, .a5] (Q := fun u => (u.gpr .a5).toNat =
      (if (word t10.mem B (arr w aX)).toNat % 2 = 0 then 1 else 0) ∧ u.mem = t10.mem) ?_ (by rfl) (by rfl))
    fun t11 ⟨⟨r11k, m11⟩, k11⟩ => ?_
  · brun [exec_li, List.append_assoc, runBlock_ptr B w, (show aX < 2048 by decide), h10.ws.s10, h10.ws.s11,
      h10.ws.scr.ld (show arr w aX + 8 ≤ Z by omega), h10.ws.scr.al8 (show arr w aX + 8 ≤ Z by omega) (by omega)]
    exact even_bit64 _
  have h11' := h10.of_keep (k11.mono (by decide))
  have xX : wordsVal t11.mem B (arr w aX) (nu n) = x := by
    rw [m11, keep_wv a10 hk0 (by decide) (fit _ nX), hx]
  have x0 : (word t10.mem B (arr w aX)).toNat % 2 = x % 2 := by
    rw [← m11, ← xX]
    obtain ⟨k, hk⟩ : ∃ k, nu n = k + 1 := ⟨nu n - 1, by omega⟩
    rw [hk]; simp only [wordsVal]; omega
  have pM : wordsVal t11.mem B (arr w aMz) (nu n) = m := by
    rw [m11, keep_wv a10 hk0 (by decide) (fit _ nM), pv9']
  -- `g = x + k m`, its carry the word `ν`.
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h11' (fun u hu => cntN_ok hu) (K := nu n) (by omega) (by omega) nG nX nM hN)
    fun t12 ⟨h12, K12, v12, p12, _, _, out12, k12⟩ => ?_
  rw [xX, pM, r11k, x0] at v12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t12.mem.writeW (off B (arr w aG + 8 * nu n))
      (t12.gpr .t4)) ?_ (by rfl) (by rfl)) fun t13 ⟨m13, k13⟩ => ?_
  · brun [p12, h12.ws.scr.st (show arr w aG + 8 * nu n + 8 ≤ Z by omega),
      h12.ws.scr.al8 (show arr w aG + 8 * nu n + 8 ≤ Z by omega) (by omega)]
  have h13 := h12.of_keep (k13.mono (by decide))
  have vG : wordsVal t13.mem B (arr w aG) (nu n + 1) = oddInput m x := by
    rw [m13, fin64_wordsVal_write_top _ _ _ _ _ (by omega)]
    unfold oddInput
    by_cases e : x % 2 = 0 <;> simp only [e, ↓reduceIte] at v12 ⊢ <;> omega
  have a13 : Keys.Frame B w [aG] [] t12.mem t13.mem := by
    rw [m13]; exact Keys.Frame.of_arr (d := 8 * nu n) (writeW_outside _ B _ (by omega)) (by omega) (by simp)
  -- `a = 0`, `b = 0`.
  rw [WP.seq_iff]
  refine WP.mono (zeroN_ok h13 nA hN) fun t14 ⟨h14, a14, z14, k14⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (zeroN_ok h14 nB hN) fun t15 ⟨h15, a15, z15, k15⟩ => ?_
  -- `b = 1`, `d = 1` and `3 ν + 2` batches.
  refine WP.mono (WP.keep [.t0, .t3, .t5, .s7] (Q := fun u => u.mem = (t15.mem.writeW (off B (arr w aB))
      (BitVec.ofNat 64 1)).writeW (off B (arr w aW)) (BitVec.ofNat 64 1) ∧
      u.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2)) ?_ (by rfl) (by rfl))
    fun t16 ⟨⟨m16, r16⟩, k16⟩ => ?_
  · brun [exec_li, wD, cntN, List.append_assoc, runBlock_ptr B w, (show aW < 2048 by decide),
      (show aB < 2048 by decide), h15.ws.s10, h15.ws.s11, h15.s8, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega),
      h15.ws.scr.st (show arr w aB + 8 ≤ Z by omega), h15.ws.scr.al8 (show arr w aB + 8 ≤ Z by omega) (by omega),
      h15.ws.scr.st (show arr w aW + 8 ≤ Z by omega), h15.ws.scr.al8 (show arr w aW + 8 ≤ Z by omega) (by omega)]
    first | (refine ⟨rfl, ?_⟩) | skip
    have : nu n = (n + 1) / 2 := rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  -- The result.
  have oB := writeW_outside t15.mem B (d := arr w aB) (BitVec.ofNat 64 1) (by omega)
  have oW := writeW_outside (t15.mem.writeW (off B (arr w aB)) (BitVec.ofNat 64 1)) B (d := arr w aW)
    (BitVec.ofNat 64 1) (by omega)
  have F16 : Keys.Frame B w [aB, aW] [] t15.mem t16.mem := by
    rw [m16]
    exact (Keys.Frame.of_arr (o := aB) (d := 0) (by simpa only [Nat.add_zero] using oB) (by omega) (by simp)).trans
      (Keys.Frame.of_arr (o := aW) (d := 0) (by simpa only [Nat.add_zero] using oW) (by omega) (by simp))
  have K11 : Keys.Frame B w [] [] t10.mem t11.mem := by rw [m11]; exact Keys.Frame.refl _ _ _ _ _
  have KF : Keys.Frame B w [aG, aA, aB, aW] [] t10.mem t16.mem :=
    (K11.mono (by simp)).trans ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans ((a14.mono (by simp)).trans
      ((a15.mono (by simp)).trans (F16.mono (by simp))))))
  have KG : Keys.Frame B w [aA, aB, aW] [] t13.mem t16.mem :=
    (a14.mono (by simp)).trans ((a15.mono (by simp)).trans (F16.mono (by simp)))
  have KA : Keys.Frame B w [aB, aW] [] t14.mem t16.mem := (a15.mono (by simp)).trans (F16.mono (by simp))
  have Kall : Keys.Frame B w [aW, aF, aG, aA, aB] [] t9.mem t16.mem := (a10.mono (by simp)).trans (KF.mono (by simp))
  have KnoW : Keys.Frame B w [aF, aG, aA, aB] [] t9.mem t15.mem :=
    (a10.mono (by simp)).trans ((K11.mono (by simp)).trans ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans
      ((a14.mono (by simp)).trans (a15.mono (by simp))))))
  have m7' : ∀ {a b : State} {rs : List Reg}, Keep rs a b → (∀ r ∈ rs, r ∈ initRegs) →
      Keep initRegs a b := fun h hr => h.mono hr
  have k : Keep initRegs t9 t16 :=
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (m7' (k10a.trans k10) (by decide))
      (m7' k11 (by decide))) (m7' (k12.trans k13) (by decide))) (m7' k14 (by decide))) (m7' k15 (by decide)))
      (m7' k16 (by decide))
  have e0 : Divstep.invRunS 59 m iv (oddInput m x) 0 = ⟨1, m, oddInput m x, 0, 1⟩ := rfl
  rw [e0]
  refine ⟨h15.of_keep7 (k16.mono (by decide)), r16, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, Kall, k⟩
  · show t16.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 1
    rw [show arr w aW + wD = arr w aW from rfl, m16, Mem.readW_writeW_self64]; rfl
  · show (wordsVal t16.mem B (arr w aF) (nu n + 1) : Int) % _ = (m : Int) % _
    rw [keep_wv KF hk1 (by decide) (fit _ nF), vF]
  · show (wordsVal t16.mem B (arr w aG) (nu n + 1) : Int) % _ = (oddInput m x : Int) % _
    rw [keep_wv KG hk1 (by decide) (fit _ nG), vG]
  · show (wordsVal t16.mem B (arr w aA) (nu n + 1) : Int) % _ = (0 : Int) % _
    rw [keep_wv KA hk1 (by decide) (fit _ nA), z14]; rfl
  · show (wordsVal t16.mem B (arr w aB) (nu n + 1) : Int) % _ = (1 : Int) % _
    have e15 : wordsVal t15.mem B (arr w aB) (nu n + 1) =
        (word t15.mem B (arr w aB)).toNat + 2 ^ 64 * wordsVal t15.mem B (arr w aB + 8) (nu n) := rfl
    have e16 : wordsVal t16.mem B (arr w aB) (nu n + 1) =
        (word t16.mem B (arr w aB)).toNat + 2 ^ 64 * wordsVal t16.mem B (arr w aB + 8) (nu n) := rfl
    have w16 : word t16.mem B (arr w aB) = BitVec.ofNat 64 1 := by
      rw [m16, oW.word (by have := arr_disj (w := w) (show aB ≠ aW by decide); omega) (by omega)]
      exact word_writeW_self _ _ _ _
    have r16' : wordsVal t16.mem B (arr w aB + 8) (nu n) = wordsVal t15.mem B (arr w aB + 8) (nu n) := by
      rw [m16, oW.wordsVal (by have := arr_disj (w := w) (show aB ≠ aW by decide); omega) (by omega),
        oB.wordsVal (by omega) (by omega)]
    rw [e16, w16, r16']
    rw [z15] at e15
    have : wordsVal t15.mem B (arr w aB + 8) (nu n) = 0 := by omega
    rw [this]; rfl
  · have w40 : 40 + 64 / 8 ≤ S w := by omega
    rw [m16, show arr w aW + wIv = arr w aW + 40 from rfl,
      Mem.readW_congr fun i hi => oW _ (by rw [ofs_off B (by omega)]; omega),
      Mem.readW_congr fun i hi => oB _ (by rw [ofs_off B (by omega)]; have := arr_disj (w := w) (show aB ≠ aW by decide); omega),
      keep_word KnoW w40 (by decide) (by simp) (fit _ nW)]
    exact hivw
  · rw [keep_wv Kall hk0 (by decide) (fit _ nM), pv9']
  · rw [keep_wv Kall hk1 (by decide) (fit _ nM), pv9]

/-- `init`: the start of the inversion modulo `m`. -/
theorem init_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n))
    (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa init s fun t => Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * nu n + 2) ∧
      (∃ iv, (m * iv + 1) % 2 ^ 64 = 0 ∧ BS t B w n m iv (Divstep.invRunS 59 m iv (oddInput m x) 0)) ∧
      Keys.Frame B w [aMz, aW, aF, aG, aA, aB] [] s.mem t.mem ∧ Keep initRegs s t := by
  have room := h.room
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nuw
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  have nX : aX < N := by unfold aX; omega
  have nM : aMz < N := by unfold aMz; omega
  rw [init, WP.seq_iff]
  refine WP.mono (initA_ok h hN hm hmn) fun t7 ⟨h7, K7, pv', pv, k7⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (initB_ok h7 pv hodd) fun t9 ⟨h9, K9, ⟨iv, hiv, hivw⟩, k9⟩ => ?_
  have K79 : Keys.Frame B w [aMz, aW] [] s.mem t9.mem := (K7.mono (by simp)).trans (K9.mono (by simp))
  have hx' : wordsVal s.mem B (arr w aX) (nu n) = x :=
    wv_low (by omega) hx (Nat.lt_of_lt_of_le hxn (pow_nu n))
  refine WP.mono (initC_ok h9 hN (x := x) (m := m) (by rw [keep_wv K79 hk0 (by decide) (fit _ nX), hx'])
    (by rw [keep_wv K9 hk1 (by decide) (fit _ nM), pv]) (by rw [keep_wv K9 hk0 (by decide) (fit _ nM), pv'])
    hivw) fun t ⟨ht, r7, st, K, kt⟩ => ?_
  exact ⟨ht, r7, ⟨iv, hiv, st⟩, (K79.mono (by simp)).trans (K.mono (by simp)),
    Keep.trans' (Keep.trans' (k7.mono (by decide)) (k9.mono (by decide))) kt⟩

/-- The run's result after `3 ν + 2` batches: `g = 0`, `|f| = gcd(m, x)` and the congruence. -/
theorem run_done {n m iv x : Nat} (hodd : m % 2 = 1) (hiv : (m * iv + 1) % 2 ^ 64 = 0)
    (hmn : m < 2 ^ (32 * n)) (hxn : x < 2 ^ (32 * n)) (hn : nu n ≤ 1024) :
    let I := Divstep.invRunS 59 m iv (oddInput m x) (3 * nu n + 2)
    I.f.natAbs = Nat.gcd m x ∧
      (x : Int) * ((if 0 ≤ I.f then 1 else -1) * I.a) * 2 ^ (5 * (3 * nu n + 2)) ≡ (Nat.gcd m x : Int) [ZMOD m] := by
  intro I
  have hmI : ((m : Int) * (iv : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hiv
  have hp := pow_nu n
  have h32 : 2 * 2 ^ (64 * nu n) ≤ 2 ^ (32 * (2 * nu n + 1)) := by
    rw [show 32 * (2 * nu n + 1) = 64 * nu n + 1 + 31 by omega, Nat.pow_add, Nat.pow_succ]
    have := Nat.one_le_two_pow (n := 31)
    calc 2 * 2 ^ (64 * nu n) = 2 ^ (64 * nu n) * 2 * 1 := by omega
      _ ≤ 2 ^ (64 * nu n) * 2 * 2 ^ 31 := Nat.mul_le_mul_left _ this
  have ox : oddInput m x ≤ m + x := by unfold oddInput; split <;> omega
  have hdone := Rsa.Divstep.done_words (w := 2 * nu n + 1) (steps := 59 * (3 * nu n + 2)) (p := m)
    (x := oddInput m x) (by omega) (by exact_mod_cast hodd) (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) (Or.inr (by exact_mod_cast Rsa.Divstep.oddInput_odd (x := x) hodd))
    (by have : m ≤ 2 ^ (32 * (2 * nu n + 1)) := by omega
        exact_mod_cast this)
    (by have : oddInput m x ≤ 2 ^ (32 * (2 * nu n + 1)) := by omega
        exact_mod_cast this) (by omega)
  rw [Int.gcd_natCast_natCast, Rsa.Divstep.oddInput_gcd] at hdone
  obtain ⟨-, hfI, hcong⟩ := Divstep.invRunS_done (N := 59) (B := 3 * nu n + 2) (by decide) hodd hmI hdone
  refine ⟨hfI, ?_⟩
  rw [show 5 * (3 * nu n + 2) = (64 - 59) * (3 * nu n + 2) by omega]
  exact hcong

/-- The inputs below `2^(32 n)`, from the contract, as the inverse's bounds. -/
theorem inputs_lt {n m x : Nat} (hmn : m < 2 ^ (32 * n)) (hxn : x < 2 ^ (32 * n)) :
    m < 2 ^ (64 * nu n) ∧ oddInput m x < 2 * 2 ^ (64 * nu n) := by
  have := pow_nu n
  have ox : oddInput m x ≤ m + x := by unfold oddInput; split <;> omega
  omega

theorem inverse_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa inverse s fun t => Ws t B Z w N ∧ Keys.Frame B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have := h.ws.wle
  have := h.nuw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nM : aMz < N := by unfold aMz; omega
  obtain ⟨pc, xc⟩ := inputs_lt hmn hxn
  have hw : 2 ^ (64 * nu n) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [inverse, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN hx hxn hm hmn hodd) fun t0 ⟨h0, r0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 r0 st0 hodd (by omega) hiv pc xc) fun t1 ⟨h1, _, st1, K1, k1⟩ => ?_
  obtain ⟨-, -, -, -, ha, -⟩ := run_bounds (k := 3 * nu n + 2) hodd hiv pc xc
  obtain ⟨hfI, hcong⟩ := run_done hodd hiv hmn hxn (by omega)
  generalize Divstep.invRunS 59 m iv (oddInput m x) (3 * nu n + 2) = I at st1 ha hfI hcong
  have gle : Nat.gcd m x ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hf1 : -(m : Int) ≤ I.f := by omega
  have hf2 : I.f ≤ m := by omega
  rw [WP.seq_iff]
  refine WP.mono (normalize_ok h1 hN st1.P1 pc st1.a ha.1 ha.2 st1.f hf1 hf2) fun t2 ⟨h2, K2, y2, c2, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (doublings_ok h2 hN (by rw [keep_wv K2 hk1 (by decide) (fit _ nM)]; exact st1.P1) rfl y2 pc)
    fun t3 ⟨h3, _, v3, K3, k3⟩ => ?_
  have hf3 : (wordsVal t3.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1)) := by
    rw [keep_wv K3 hk1 (by decide) (fit _ nF), keep_wv K2 hk1 (by decide) (fit _ nF)]; exact st1.f
  have hyr := Rsa.Divstep.doubled_lt (p := m) (a := wordsVal t2.mem B (arr w aA) (nu n + 1))
    (k := 5 * (3 * nu n + 2)) (by omega)
  rw [finish, WP.seq_iff]
  refine WP.mono (finishG_ok h3 hN hf3 (by rw [hfI]; omega)) fun t4 ⟨h4, K4, g4, k4⟩ => ?_
  refine WP.mono (finishY_ok h4 hN (y := Rsa.Divstep.doubled m (wordsVal t2.mem B (arr w aA) (nu n + 1))
    (5 * (3 * nu n + 2))) (by rw [keep_wv K4 hk1 (by decide) (fit _ nA)]; exact v3) (by omega))
    fun t5 ⟨h5, K5, y5, k5⟩ => ?_
  refine ⟨h5.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K3.mono (by decide)).trans ((K4.mono (by decide)).trans (K5.mono (by decide))))))),
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' k0 k1) (k2.mono (by decide))) k3)
      (k4.mono (by decide))) (k5.mono (by decide)), fun _ => ?_⟩
  have g5 : num t5.mem B w 1 = I.f.natAbs := by
    rw [show (1 : Nat) = aGcd from rfl, ← g4]; exact Keys.Frame.num K5 (by decide) (by simp) (fit _ (by unfold aGcd; omega))
  rw [show aY = 3 from rfl] at y5
  rw [g5, y5, hfI]
  refine ⟨Nat.gcd_comm _ _, ?_, hyr⟩
  have e : ((Rsa.Divstep.doubled m (wordsVal t2.mem B (arr w aA) (nu n + 1)) (5 * (3 * nu n + 2)) : Nat) : Int) * x ≡
      (Nat.gcd m x : Int) [ZMOD m] := by
    unfold Rsa.Divstep.doubled
    refine Int.ModEq.trans ?_ hcong
    push_cast
    have h1 : ((wordsVal t2.mem B (arr w aA) (nu n + 1) : Int) * 2 ^ (5 * (3 * nu n + 2))) % m * x ≡
        (wordsVal t2.mem B (arr w aA) (nu n + 1) : Int) * 2 ^ (5 * (3 * nu n + 2)) * x [ZMOD m] :=
      (Int.mod_modEq _ _).mul_right _
    refine h1.trans ?_
    have h2 := (c2.mul_right ((2 : Int) ^ (5 * (3 * nu n + 2)))).mul_right (x : Int)
    refine h2.trans ?_
    rw [show (if 0 ≤ I.f then 1 else -1) * I.a * 2 ^ (5 * (3 * nu n + 2)) * (x : Int) =
      (x : Int) * ((if 0 ≤ I.f then 1 else -1) * I.a) * 2 ^ (5 * (3 * nu n + 2)) by ring]
  exact e.symm.dvd

theorem inverseS_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa inverseS s fun t => Ws t B Z w N ∧ Keys.Frame B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ ((num t.mem B w 3 * 2 ^ (5 * (3 * nu n + 2)) % m : Nat) : Int) * x - num t.mem B w 1 ∧
        num t.mem B w 3 < m) := by
  have := h.ws.wle
  have := h.nuw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nM : aMz < N := by unfold aMz; omega
  obtain ⟨pc, xc⟩ := inputs_lt hmn hxn
  have hw : 2 ^ (64 * nu n) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [inverseS, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN hx hxn hm hmn hodd) fun t0 ⟨h0, r0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 r0 st0 hodd (by omega) hiv pc xc) fun t1 ⟨h1, _, st1, K1, k1⟩ => ?_
  obtain ⟨-, -, -, -, ha, -⟩ := run_bounds (k := 3 * nu n + 2) hodd hiv pc xc
  obtain ⟨hfI, hcong⟩ := run_done hodd hiv hmn hxn (by omega)
  generalize Divstep.invRunS 59 m iv (oddInput m x) (3 * nu n + 2) = I at st1 ha hfI hcong
  have gle : Nat.gcd m x ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hf1 : -(m : Int) ≤ I.f := by omega
  have hf2 : I.f ≤ m := by omega
  rw [WP.seq_iff]
  refine WP.mono (normalize_ok h1 hN st1.P1 pc st1.a ha.1 ha.2 st1.f hf1 hf2) fun t2 ⟨h2, K2, y2, c2, k2⟩ => ?_
  have hf3 : (wordsVal t2.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1)) := by
    rw [keep_wv K2 hk1 (by decide) (fit _ nF)]; exact st1.f
  rw [finish, WP.seq_iff]
  refine WP.mono (finishG_ok h2 hN hf3 (by rw [hfI]; omega)) fun t4 ⟨h4, K4, g4, k4⟩ => ?_
  refine WP.mono (finishY_ok h4 hN (y := wordsVal t2.mem B (arr w aA) (nu n + 1))
    (by rw [keep_wv K4 hk1 (by decide) (fit _ nA)]) (by omega))
    fun t5 ⟨h5, K5, y5, k5⟩ => ?_
  refine ⟨h5.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K4.mono (by decide)).trans (K5.mono (by decide)))))),
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' k0 k1) (k2.mono (by decide)))
      (k4.mono (by decide))) (k5.mono (by decide)), fun _ => ?_⟩
  have g5 : num t5.mem B w 1 = I.f.natAbs := by
    rw [show (1 : Nat) = aGcd from rfl, ← g4]; exact Keys.Frame.num K5 (by decide) (by simp) (fit _ (by unfold aGcd; omega))
  rw [show aY = 3 from rfl] at y5
  rw [g5, y5, hfI]
  refine ⟨Nat.gcd_comm _ _, ?_, y2⟩
  have e : ((wordsVal t2.mem B (arr w aA) (nu n + 1) * 2 ^ (5 * (3 * nu n + 2)) % m : Nat) : Int) * x ≡
      (Nat.gcd m x : Int) [ZMOD m] := by
    refine Int.ModEq.trans ?_ hcong
    push_cast
    have h1 : ((wordsVal t2.mem B (arr w aA) (nu n + 1) : Int) * 2 ^ (5 * (3 * nu n + 2))) % m * x ≡
        (wordsVal t2.mem B (arr w aA) (nu n + 1) : Int) * 2 ^ (5 * (3 * nu n + 2)) * x [ZMOD m] :=
      (Int.mod_modEq _ _).mul_right _
    refine h1.trans ?_
    have h2 := (c2.mul_right ((2 : Int) ^ (5 * (3 * nu n + 2)))).mul_right (x : Int)
    refine h2.trans ?_
    rw [show (if 0 ≤ I.f then 1 else -1) * I.a * 2 ^ (5 * (3 * nu n + 2)) * (x : Int) =
      (x : Int) * ((if 0 ≤ I.f then 1 else -1) * I.a) * 2 ^ (5 * (3 * nu n + 2)) by ring]
  exact e.symm.dvd

theorem gcd_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa gcd s fun t => Ws t B Z w N ∧ Keys.Frame B w gcdArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m) := by
  have := h.ws.wle
  have := h.nuw
  have room := h.room
  obtain ⟨pc, xc⟩ := inputs_lt hmn hxn
  simp only [gcd, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN hx hxn hm hmn hodd) fun t0 ⟨h0, r0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loopG_ok hN h0 r0 st0.toBG hodd hiv pc xc) fun t1 ⟨h1, _, st1, K1, k1⟩ => ?_
  obtain ⟨hfI, -⟩ := run_done hodd hiv hmn hxn (by omega)
  have gle : Nat.gcd m x ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  refine WP.mono (finishG_ok h1 hN st1.f (by rw [hfI]; omega)) fun t2 ⟨h2, K2, g2, k2⟩ => ?_
  refine ⟨h2.ws, (K0.mono (by decide)).trans ((K1.mono (by decide)).trans (K2.mono (by decide))),
    Keep.trans' (Keep.trans' k0 k1) (k2.mono (by decide)), fun _ => ?_⟩
  rw [show (1 : Nat) = aGcd from rfl, g2, hfI, Nat.gcd_comm]

end VG.Proof.Rsa.RISCV64.InvBatch

namespace VG.Proof.Rsa.RISCV64

/-- The batched inverse's and GCD's contract, supplied at the registrations. -/
instance invLaw : InvLaw where
  inverse_ok := InvBatch.inverse_ok
  inverseS_ok := InvBatch.inverseS_ok
  gcd_ok := InvBatch.gcd_ok

end VG.Proof.Rsa.RISCV64
