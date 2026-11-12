module
-- separate module: it imports the batches' and the end's proofs, which only the registrations reach

public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.Divstep.Bound
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
public import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
public import VerifiedGarbage.Proof.Divstep.TcSLaw
import VerifiedGarbage.Proof.Divstep.WordArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Ring.Abs
public import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.RangeCover
import Mathlib.Tactic.NormNum
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw

/-!
# The batched inverse on PPC64LE

A batch (`batch_ok`) is `Proof/Divstep/BatchS.lean`'s `batchS 59` on the window
and the arrays; `loop_ok`: `3 ν + 2` batches from the start of the inversion,
counted in `r10`, as `invRunS 59`; the end (`normalize_ok`, `doublings_ok`,
`finishG_ok`, `finishY_ok`), the start (`init_ok`), and `inverse_ok`,
`inverseS_ok`: `InvLaw`, whose instance the registrations take from here, given
`TcSLaw` (from `Proof/Divstep/TcSBounds.lean`), so that only they import the
batches' algebra.
-/

@[expose] public section


namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)
open VG.Proof.Divstep (MSt msteps WSt)
open VG.Proof.Rsa.PPC64LE.Loops (sgn FGAcc ABAcc fg_init ab_init fgLoop_ok abLoop?_ok wv_step2 wv_step2' lo2 hi2
  macC abRegs wordsVal_write_top)

/-! ## Frames -/

/-- A number of `k + 1` words is its low word modulo `2^59`. -/
theorem low59 {m : Mem} {B : Addr} {d k : Nat} {x : Int}
    (h : (wordsVal m B d (k + 1) : Int) % 2 ^ (64 * (k + 1)) = x % 2 ^ (64 * (k + 1))) :
    ((word m B d).toNat : Int) % 2 ^ 59 = x % 2 ^ 59 := by
  have hW : wordsVal m B d (k + 1) = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) k := rfl
  have hdvd : (2 : Int) ^ 59 ∣ 2 ^ (64 * (k + 1)) := pow_dvd_pow 2 (by omega)
  rw [← Int.emod_emod_of_dvd x hdvd, ← h, Int.emod_emod_of_dvd _ hdvd, hW]
  push_cast
  omega


/-- A combination of congruent numbers. -/
theorem cong_comb {Q u v X Y f g : Int} (hX : X % Q = f % Q) (hY : Y % Q = g % Q) :
    (u * X + v * Y) % Q = (u * f + v * g) % Q :=
  Int.ModEq.add (Int.ModEq.mul_left u hX) (Int.ModEq.mul_left v hY)

/-! ## The divsteps -/

/-- A 64-bit word outside the bytes that changed. -/
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
theorem save_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n c) :
    WP isa (.block save) t fun u => (u.mem = ((((t.mem.writeW (off B (arr w aW)) (t.gpr .r3)).writeW
      (off B (arr w aW + 8)) (t.gpr .r6)).writeW (off B (arr w aW + 16)) (t.gpr .r7)).writeW
      (off B (arr w aW + 24)) (t.gpr .r8)).writeW (off B (arr w aW + 32)) (t.gpr .r9)) ∧ Keep [.r4] t u := by
  have hW : aW < N := by have := h.room; unfold aW; omega
  have fW := h.ws.arr_fit hW
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  refine WP.keep _ ?_ (by decide)
  have hs := h.ws.scr
  prun [save, ptr, wD, wU, wV, wQ, wR, exec_li (imm := aW) (by decide),
    exec_addi (n := .r4) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h.ptr aW,
    (hs.congr (by rfl)).st (show arr w aW + 8 ≤ Z by omega), hs.st (show arr w aW + 8 + 8 ≤ Z by omega),
    hs.st (show arr w aW + 16 + 8 ≤ Z by omega), hs.st (show arr w aW + 24 + 8 ≤ Z by omega),
    hs.st (show arr w aW + 32 + 8 ≤ Z by omega)]

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
theorem head_ok {s : State} {B : Addr} {Z w N n c : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n c) (hst : BG s B w n I) (hN : N ≤ 256)
    (hd : |I.d| + 2 * 59 < 2 ^ 62) (hf : I.f % 2 = 1) :
    WP isa (.block (start ++ wsteps 59 ++ save)) s fun t => Ctx t B Z w N n c ∧
      KeyWorkspace.Keep B w [aW] [] s.mem t.mem ∧ Outside B (arr w aW) 40 s.mem t.mem ∧
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
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The start: the low words, `d` and the identity.
  have hs1 : WP isa (.block start) s fun t => (regsW t = ⟨BitVec.ofInt 64 I.d,
      word s.mem B (arr w aF), word s.mem B (arr w aG),
      BitVec.ofNat 64 1, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 1⟩ ∧ t.mem = s.mem) ∧
      Keep kRegs s t := by
    have hd0 : s.mem.readW (off B (arr w aW)) 64 = BitVec.ofInt 64 I.d := by
      simpa only [wD, Nat.add_zero] using hst.d
    refine WP.keep _ ?_ (by decide)
    prun [start, ldW, ptr, regsW, wD, word, exec_load_d, exec_li (imm := aF) (by decide),
      exec_li (imm := aG) (by decide), exec_li (imm := aW) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      exec_addi (n := .r3) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      hdr_eq, h.ptr aF, h.ptr aG, h.ptr aW, h.ws.scr.ld (show arr w aF + 8 ≤ Z by omega),
      h.ws.scr.ld (show arr w aG + 8 ≤ Z by omega), h.ws.scr.ld (show arr w aW + 8 ≤ Z by omega), hd0]
  refine WP.mono hs1 fun t1 ⟨⟨r1, m1⟩, k1⟩ => ?_
  refine WP.mono (wsteps_ok 59 t1) fun t2 ⟨⟨r2, m2⟩, k2⟩ => ?_
  have h2 := h.of_keep (k1.trans' k2)
  -- The words of the divsteps.
  have rel : (regsW t1).rel (MSt.init I.d I.f I.g) 59 := by
    rw [r1]
    exact ⟨rfl, rfl, rfl, rfl, rfl, low59 hst.f, low59 hst.g⟩
  have R := Divstep.wsteps_rel (by decide) rel (by simpa [MSt.init] using hd) hf 59 (Nat.le_refl _)
  rw [← r2] at R
  obtain ⟨Rd, Ru, Rv, Rq, Rr, -, -⟩ := R
  refine WP.mono (save_ok h2) fun t3 ⟨m3, k3⟩ => ?_
  obtain ⟨e0, e1, e2, e3, e4, out⟩ := save_read t2.mem B (arr w aW) (by omega) (t2.gpr .r3) (t2.gpr .r6)
    (t2.gpr .r7) (t2.gpr .r8) (t2.gpr .r9)
  rw [← m3] at e0 e1 e2 e3 e4 out
  rw [m2, m1] at out
  have k : Keep kRegs s t3 := (k1.trans' k2).trans' (k3.mono (by decide))
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega)
    (by simp), out, ?_, ?_, ?_, ?_, ?_, k⟩
  · simpa only [wD, Nat.add_zero] using e0.trans Rd
  · exact e1.trans Ru
  · exact e2.trans Rv
  · exact e3.trans Rq
  · exact e4.trans Rr

/-! ## The arithmetic of the updates -/

theorem pow_succ64 (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- The new `f` or `g` as `Divstep.TcSLaw.shr_nat` reads it: the shift of `y = 2^59 z`. -/
theorem shr_val [Divstep.TcSLaw] {D V k : Nat} {y z : Int}
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
  exact Divstep.TcSLaw.shr_nat (H := 2 ^ (64 * k) * 2 ^ 63) (V := V) (D := D) (c := 2 ^ 59) (B := 2 ^ 64)
    rfl rfl (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (by rw [← e2]; exact hV) hT hy.1 hy.2 hz hD

/-- The new `a` or `b` as `Divstep.TcSLaw.mredRaw_nat` reads it. -/
theorem mred_val [Divstep.TcSLaw] {R W w0 k p iv : Nat} {t : Int}
    (hR : R = (W + 2 ^ (64 * k) * 2 ^ 64 * (if 2 ^ (64 * k) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) +
      w0 * iv % 2 ^ 64 * p) % (2 ^ (64 * k) * 2 ^ 64 * 2 ^ 64) / 2 ^ 64)
    (hw0 : W % 2 ^ 64 = w0) (hW : W < 2 ^ (64 * (k + 1)))
    (hT : (W : Int) % 2 ^ (64 * (k + 1)) = t % 2 ^ (64 * (k + 1)))
    (hp : 0 < p) (hpA : p < 2 ^ (64 * k)) (hm : (p * iv + 1) % 2 ^ 64 = 0) (ht : |t| ≤ 2 ^ 63 * p) :
    (R : Int) % 2 ^ (64 * (k + 1)) = Divstep.mredRaw p iv t % 2 ^ (64 * (k + 1)) := by
  have eAB : (2 : Int) ^ (64 * (k + 1)) = ((2 ^ (64 * k) * 2 ^ 64 : Nat) : Int) := by
    rw [← pow_succ64]; push_cast; rfl
  rw [eAB] at hT ⊢
  exact Divstep.TcSLaw.mredRaw_nat (A := 2 ^ (64 * k)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := iv) (W := W)
    (k := w0 * iv % 2 ^ 64) (t := t)
    (E := (W + 2 ^ (64 * k) * 2 ^ 64 * (if 2 ^ (64 * k) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) +
      w0 * iv % 2 ^ 64 * p) % (2 ^ (64 * k) * 2 ^ 64 * 2 ^ 64))
    (R := R) rfl rfl (Nat.two_pow_pos _) hp hpA hm ht (by rw [← pow_succ64]; exact hW) hT
    (by rw [hw0]) rfl hR

/-- A batch's combination of `f` and `g` of at most `2^(64 ν + 3)`, in the
half range of `ν + 1` words. -/
theorem comb_half [Divstep.TcSLaw] {u v f g : Int} {k : Nat} (huv : |u| + |v| ≤ 2 ^ 59)
    (hf : |f| ≤ 2 ^ (64 * k) * 2 ^ 3) (hg : |g| ≤ 2 ^ (64 * k) * 2 ^ 3) :
    -((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) ≤ u * f + v * g ∧
      u * f + v * g < ((2 ^ (64 * k) * 2 ^ 63 : Nat) : Int) := by
  have := Divstep.TcSLaw.comb_le huv hf hg
  rw [abs_le] at this
  have hA : (0 : Int) < 2 ^ (64 * k) := by positivity
  push_cast
  constructor <;> nlinarith

/-- The coefficients of a batch are at most `2^61`. -/
theorem natAbs61 {u v : Int} (h : |u| + |v| ≤ 2 ^ 59) : u.natAbs ≤ 2 ^ 61 ∧ v.natAbs ≤ 2 ^ 61 := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h; omega

/-! ## The updates -/

/-- The registers the updates change: `kRegs` and the borrowed ones. -/
abbrev bRegs : List Reg := kRegs ++ (spill1 ++ spill2 ++ spill3)

theorem toInt_mat {x : Int} (h : x.natAbs ≤ 2 ^ 61) : (BitVec.ofInt 64 x).toInt = x :=
  BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)

/-- `updateG`: the new `f` and `g` from the matrix in the window, in place. -/
theorem updateG_ok [Divstep.TcSLaw] {s : State} {B : Addr} {Z w N n c : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hf : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1)))
    (hg : (wordsVal s.mem B (arr w aG) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.g % 2 ^ (64 * (nu n + 1)))
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat I).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat I).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat I).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat I).r)
    (hodd : I.f % 2 = 1) (hF : |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3) :
    WP isa updateG s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aF, aG] [] s.mem t.mem ∧
      (wordsVal t.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        ((mat I).u * I.f + (mat I).v * I.g) / 2 ^ 59 % 2 ^ (64 * (nu n + 1)) ∧
      (wordsVal t.mem B (arr w aG) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        ((mat I).q * I.f + (mat I).r * I.g) / 2 ^ 59 % 2 ^ (64 * (nu n + 1)) ∧
      Keep bRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.wbig
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  obtain ⟨ef, eg⟩ := Divstep.msteps_mat (d := I.d) (g := I.g) hodd 59
  have z₁ : (mat I).u * I.f + (mat I).v * I.g = 2 ^ 59 * (((mat I).u * I.f + (mat I).v * I.g) / 2 ^ 59) := by
    rw [← ef, Int.mul_ediv_cancel_left _ (by norm_num)]
  have z₂ : (mat I).q * I.f + (mat I).r * I.g = 2 ^ 59 * (((mat I).q * I.f + (mat I).r * I.g) / 2 ^ 59) := by
    rw [← eg, Int.mul_ediv_cancel_left _ (by norm_num)]
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have fF := h.ws.arr_fit nF
  have fG := h.ws.arr_fit nG
  have eFG : arr w aF + S w ≤ arr w aG := KeyWorkspace.arr_end (by decide)
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  have u1 := (natAbs61 bu).1
  have u2 := (natAbs61 bu).2
  have q1 := (natAbs61 bq).1
  have q2 := (natAbs61 bq).2
  have tu := toInt_mat u1
  have tv := toInt_mat u2
  have tq := toInt_mat q1
  have tr := toInt_mat q2
  simp only [updateG, seqs]
  rw [WP.seq_iff, show fsetup aF aG ++ fterms 0 ++ ([.lsr .d .r28 .r22 59, .lsr .d .r12 .r24 59] : List Instr) ++
      fshift .r22 .r23 ++ fshift .r24 .r25 ++ cntN = fsetup aF aG ++ ((fterms 0 ++
      ([.lsr .d .r28 .r22 59, .lsr .d .r12 .r24 59] : List Instr) ++ fshift .r22 .r23 ++ fshift .r24 .r25) ++ cntN)
    by simp only [List.append_assoc], WP.block_append_iff]
  -- The matrix, its masks, the pointers.
  refine WP.mono (fsetup_ok h (a := aF) (b := aG) (by decide) (by decide))
    fun v ⟨hv, mv, v14, v15, v16, v17, m18, m19, m20, m21, v5, v6, z22, z23, z24, z25, kv⟩ => ?_
  rw [hU] at v14
  rw [hV] at v15
  rw [hQ] at v16
  rw [hR] at v17
  rw [WP.block_append_iff]
  -- Word 0.
  refine WP.mono (fgFirst_ok hv.ws.scr v5 v6 (by omega) (by omega) m18 m19 m20 m21)
    fun x ⟨⟨x22, x23, x28, x24, x25, x12, xm⟩, kx⟩ => ?_
  have hx := hv.of_keep' kx
  refine WP.mono (cntN_ok hx) fun y ⟨⟨y8, ym⟩, ky⟩ => ?_
  have hy := hx.of_keep' ky
  have g : ∀ r, r ∉ [Reg.r0, .r3, .r12, .r22, .r23, .r24, .r25, .r26, .r27, .r28] → r ≠ .r8 → y.gpr r = v.gpr r :=
    fun r h1 h2 => (ky.gpr _ (by simp [h2])).trans (kx.gpr _ h1)
  have kyr : ∀ r, r ≠ .r8 → y.gpr r = x.gpr r := fun r hr => ky.gpr _ (by simp [hr])
  have y14 : y.gpr .r14 = BitVec.ofInt 64 (mat I).u := (g .r14 (by decide) (by decide)).trans v14
  have y15 : y.gpr .r15 = BitVec.ofInt 64 (mat I).v := (g .r15 (by decide) (by decide)).trans v15
  have y16 : y.gpr .r16 = BitVec.ofInt 64 (mat I).q := (g .r16 (by decide) (by decide)).trans v16
  have y17 : y.gpr .r17 = BitVec.ofInt 64 (mat I).r := (g .r17 (by decide) (by decide)).trans v17
  have y18 : y.gpr .r18 = sgn (y.gpr .r14) := by
    rw [g .r18 (by decide) (by decide), m18, g .r14 (by decide) (by decide)]
  have y19 : y.gpr .r19 = sgn (y.gpr .r15) := by
    rw [g .r19 (by decide) (by decide), m19, g .r15 (by decide) (by decide)]
  have y20 : y.gpr .r20 = sgn (y.gpr .r16) := by
    rw [g .r20 (by decide) (by decide), m20, g .r16 (by decide) (by decide)]
  have y21 : y.gpr .r21 = sgn (y.gpr .r17) := by
    rw [g .r21 (by decide) (by decide), m21, g .r17 (by decide) (by decide)]
  have em : y.mem = s.mem := ym.trans (xm.trans mv)
  have wv1 : ∀ d, wordsVal y.mem B d 1 = (word v.mem B d).toNat := fun d => by
    rw [ym, xm]; simp [wordsVal]
  have y5 : y.gpr .r5 = off B (arr w aF) := (g .r5 (by decide) (by decide)).trans v5
  have y6 : y.gpr .r6 = off B (arr w aG) := (g .r6 (by decide) (by decide)).trans v6
  have i1 : FGAcc (y.gpr .r14).toInt (y.gpr .r15).toInt (wordsVal y.mem B (arr w aF) 1)
      (wordsVal y.mem B (arr w aG) 1) 0 0 (y.gpr .r22) (y.gpr .r23) (y.gpr .r28) := by
    rw [wv1, wv1, kyr .r22 (by decide), x22, kyr .r23 (by decide), x23, kyr .r28 (by decide), x28,
      g .r14 (by decide) (by decide), g .r15 (by decide) (by decide)]
    exact fg_init _ _ _ _ _ _ z22 z23 (by rw [v14, tu]; omega) (by rw [v14, tu]; omega) (by rw [v15, tv]; omega)
      (by rw [v15, tv]; omega)
  have i2 : FGAcc (y.gpr .r16).toInt (y.gpr .r17).toInt (wordsVal y.mem B (arr w aF) 1)
      (wordsVal y.mem B (arr w aG) 1) 0 0 (y.gpr .r24) (y.gpr .r25) (y.gpr .r12) := by
    rw [wv1, wv1, kyr .r24 (by decide), x24, kyr .r25 (by decide), x25, kyr .r12 (by decide), x12,
      g .r16 (by decide) (by decide), g .r17 (by decide) (by decide)]
    exact fg_init _ _ _ _ _ _ z24 z25 (by rw [v16, tq]; omega) (by rw [v16, tq]; omega) (by rw [v17, tr]; omega)
      (by rw [v17, tr]; omega)
  -- Words `1 … ν`.
  rw [WP.seq_iff]
  refine WP.mono (fgLoop_ok (dF := arr w aF) (dG := arr w aG) hy.ws.scr y5 y6 y8 (by omega) (by omega)
    (by omega) (by omega) (by omega) y18 y19 y20 y21
    (by rw [y14, tu]; omega) (by rw [y14, tu]; omega) (by rw [y15, tv]; omega) (by rw [y15, tv]; omega)
    (by rw [y16, tq]; omega) (by rw [y16, tq]; omega) (by rw [y17, tr]; omega) (by rw [y17, tr]; omega)
    i1 i2) fun z ⟨za, zb, z5, z6, zout, kz⟩ => ?_
  have hz := hy.of_keep' kz
  -- The top words.
  refine WP.mono (fgTop_ok hz.ws.scr z5 z6 (by omega) (by omega)) fun t1 ⟨m1, k1⟩ => ?_
  -- The frame.
  have Kz : KeyWorkspace.Keep B w [aF, aG] [] y.mem z.mem :=
    Outs.cover zout fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(arr w aF, S w), by simp [KeyWorkspace.ranges], by simp, by simp; omega⟩
      · exact ⟨(arr w aG, S w), by simp [KeyWorkspace.ranges], by simp, by simp; omega⟩
  have K1 : KeyWorkspace.Keep B w [aF, aG] [] z.mem t1.mem := by
    rw [m1]
    exact (KeyWorkspace.Keep.of_arr (o := aF) (d := 8 * nu n) (writeW_outside _ B _ (by omega)) (by omega)
      (by simp)).trans
      (KeyWorkspace.Keep.of_arr (o := aG) (d := 8 * nu n) (writeW_outside _ B _ (by omega)) (by omega) (by simp))
  have kk : Keep bRegs s t1 := ((((kv.trans kx).trans ky).trans kz).trans k1).mono (by decide)
  refine ⟨h.of_keep' kk, by rw [← em]; exact Kz.trans K1, ?_, ?_, kk⟩
  -- The values.
  · obtain ⟨V, hV, hT, hD⟩ := fg_end za (wordsVal_lt _ _ _ _)
    rw [y14, y15, tu, tv, em, cong_comb hf hg] at hT
    rw [m1, wv_step2 _ _ _ (by omega) (by omega) (by omega)]
    exact shr_val hD hV hT (comb_half bu hF hG) z₁
  · obtain ⟨V, hV, hT, hD⟩ := fg_end zb (wordsVal_lt _ _ _ _)
    rw [y16, y17, tq, tr, em, cong_comb hf hg] at hT
    rw [m1, wv_step2' _ _ _ (by omega),
      (writeW_outside _ B _ (d := arr w aF + 8 * nu n) (by omega)).wordsVal (by omega) (by omega)]
    exact shr_val hD hV hT (comb_half bq hF hG) z₂

/-- A word of the first of two arrays, at or after the words written. -/
theorem outs2_word {B : Addr} {m m' : Mem} {d e j i : Nat} (h : Outs B [(d, 8 * j), (e, 8 * j)] m m')
    (hi : j ≤ i) (hsep : d + 8 * i + 8 ≤ e ∨ e + 8 * j ≤ d + 8 * i) (fit : d + 8 * i + 8 ≤ 2 ^ 64) :
    word m' B (d + 8 * i) = word m B (d + 8 * i) :=
  Outs.word h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) fit

/-- The same, of the second array. -/
theorem outs2_word' {B : Addr} {m m' : Mem} {d e j i : Nat} (h : Outs B [(d, 8 * j), (e, 8 * j)] m m')
    (hi : j ≤ i) (hsep : e + 8 * i + 8 ≤ d ∨ d + 8 * j ≤ e + 8 * i) (fit : e + 8 * i + 8 ≤ 2 ^ 64) :
    word m' B (e + 8 * i) = word m B (e + 8 * i) :=
  Outs.word h (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) fit

/-- Words `j` and `j + 1` of a number stored. -/
theorem wv_top2 (m : Mem) (B : Addr) (d j : Nat) (a b : BitVec 64) (h : d + 8 * j + 16 ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * j)) a).writeW (off B (d + 8 * j + 8)) b) B d (j + 2) =
      wordsVal m B d j + 2 ^ (64 * j) * a.toNat + 2 ^ (64 * (j + 1)) * b.toNat := by
  rw [show j + 2 = j + 1 + 1 from rfl, show d + 8 * j + 8 = d + 8 * (j + 1) by omega,
    wordsVal_write_top _ _ _ _ _ (by omega), wordsVal_write_top _ _ _ _ _ (by omega)]

/-- Two words stored apart from a number. -/
theorem wv_apart2 (m : Mem) (B : Addr) {d e K : Nat} (a b : BitVec 64) (he : e + 16 ≤ 2 ^ 64)
    (hd : d + 8 * K ≤ e ∨ e + 16 ≤ d) (hd' : d + 8 * K ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B e) a).writeW (off B (e + 8)) b) B d K = wordsVal m B d K := by
  rw [(writeW_outside _ B b (d := e + 8) (by omega)).wordsVal (by omega) hd',
    (writeW_outside _ B a (d := e) (by omega)).wordsVal (by omega) hd']

/-- The end of the pass over `a` and `b` as `mredRaw` reads it: the stored
words with the last two, for an accumulator over the words of `a` and `b`
(`FA`, `FB`, `ν + 1` of them, `ν = k + 1`). -/
theorem ab_mred [Divstep.TcSLaw] {c1 c2 : BitVec 64} {u v IA IB : Int} {K w0 Da Db P k R p iv FA FB : Nat}
    {lo hi c x y : BitVec 64} (hu : c1.toInt = u) (hv : c2.toInt = v) (hu1 : u.natAbs ≤ 2 ^ 61)
    (hv1 : v.natAbs ≤ 2 ^ 61) (h : ABAcc c1.toInt c2.toInt K w0 Da Db P k R lo hi c) (hR : R < 2 ^ (64 * k))
    (hDA : Da + 2 ^ (64 * (k + 1)) * x.toNat = FA) (hDB : Db + 2 ^ (64 * (k + 1)) * y.toNat = FB)
    (hA : (FA : Int) % 2 ^ (64 * (k + 1 + 1)) = IA % 2 ^ (64 * (k + 1 + 1)))
    (hB : (FB : Int) % 2 ^ (64 * (k + 1 + 1)) = IB % 2 ^ (64 * (k + 1 + 1)))
    (hK : K = w0 * iv % 2 ^ 64) (hP : P = p) (hp : 0 < p) (hpA : p < 2 ^ (64 * (k + 1)))
    (hm : (p * iv + 1) % 2 ^ 64 = 0) (ht : |u * IA + v * IB| ≤ 2 ^ 63 * p) :
    ((R + 2 ^ (64 * k) * (lastLo (lo2 c1 c2 x y lo) c).toNat + 2 ^ (64 * (k + 1)) *
        (lastHi (lo2 c1 c2 x y lo) c).toNat : Nat) : Int) % 2 ^ (64 * (k + 1 + 1)) =
      Divstep.mredRaw p iv (u * IA + v * IB) % 2 ^ (64 * (k + 1 + 1)) := by
  obtain ⟨W, hW, hw0, hT, hRv⟩ := ab_end x y (by rw [hu]; omega) (by rw [hu]; omega) (by rw [hv]; omega)
    (by rw [hv]; omega) h hR
  rw [hu, hv, hDA, hDB, show 64 * (k + 2) = 64 * (k + 1 + 1) by omega, cong_comb hA hB] at hT
  rw [hK, hP] at hRv
  rw [hRv]
  exact mred_val rfl hw0 hW hT hp hpA hm ht

/-- The start of `updateAB`: the matrix, its masks, the pointers, word 0 and
the count of the words between. -/
theorem updateAB_head {s : State} {B : Addr} {Z w N n c p iv k : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n c) (hN : N ≤ 256) (hkν : nu n = k + 1)
    (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) (hP : wordsVal s.mem B (arr w aMz) (nu n) = p)
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat I).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat I).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat I).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat I).r)
    (hm : (p * iv + 1) % 2 ^ 64 = 0) :
    WP isa (.block (fsetup aA aB ++ ptr .r7 aMz ++ ldW .r4 wIv ++ abFirst ++ cntN ++
      ([.subi .r8 .r8 1] : List Instr))) s fun y =>
      ∃ w1 w2 : Nat, Keep bRegs s y ∧ y.mem = s.mem ∧ Ctx y B Z w N n c ∧
        y.gpr .r5 = off B (arr w aA) ∧ y.gpr .r6 = off B (arr w aB) ∧ y.gpr .r7 = off B (arr w aMz) ∧
        y.gpr .r8 = BitVec.ofNat 64 k ∧
        y.gpr .r14 = BitVec.ofInt 64 (mat I).u ∧ y.gpr .r15 = BitVec.ofInt 64 (mat I).v ∧
        y.gpr .r16 = BitVec.ofInt 64 (mat I).q ∧ y.gpr .r17 = BitVec.ofInt 64 (mat I).r ∧
        y.gpr .r18 = sgn (y.gpr .r14) ∧ y.gpr .r19 = sgn (y.gpr .r15) ∧
        y.gpr .r20 = sgn (y.gpr .r16) ∧ y.gpr .r21 = sgn (y.gpr .r17) ∧
        (y.gpr .r28).toNat = w1 * iv % 2 ^ 64 ∧ (y.gpr .r12).toNat = w2 * iv % 2 ^ 64 ∧
        ABAcc (y.gpr .r14).toInt (y.gpr .r15).toInt (y.gpr .r28).toNat w1 (wordsVal y.mem B (arr w aA) 1)
          (wordsVal y.mem B (arr w aB) 1) (wordsVal y.mem B (arr w aMz) 1) 0 0 (y.gpr .r22) (y.gpr .r23) (y.gpr .r9) ∧
        ABAcc (y.gpr .r16).toInt (y.gpr .r17).toInt (y.gpr .r12).toNat w2 (wordsVal y.mem B (arr w aA) 1)
          (wordsVal y.mem B (arr w aB) 1) (wordsVal y.mem B (arr w aMz) 1) 0 0 (y.gpr .r24) (y.gpr .r25)
          (y.gpr .r11) := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.wbig
  have := h.ws.wle
  have hnw := h.ws.nowrap
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have nM : aMz < N := by unfold aMz; omega
  have fA := h.ws.arr_fit nA
  have fB := h.ws.arr_fit nB
  have fM := h.ws.arr_fit nM
  have u1 := (natAbs61 bu).1
  have u2 := (natAbs61 bu).2
  have q1 := (natAbs61 bq).1
  have q2 := (natAbs61 bq).2
  have tu := toInt_mat u1
  have tv := toInt_mat u2
  have tq := toInt_mat q1
  have tr := toInt_mat q2
  rw [show fsetup aA aB ++ ptr .r7 aMz ++ ldW .r4 wIv ++ abFirst ++ cntN ++ ([.subi .r8 .r8 1] : List Instr) =
      fsetup aA aB ++ (ptr .r7 aMz ++ (ldW .r4 wIv ++ (abFirst ++ (cntN ++ ([.subi .r8 .r8 1] : List Instr)))))
    by simp only [List.append_assoc], WP.block_append_iff]
  -- The matrix, its masks, the pointers.
  refine WP.mono (fsetup_ok h (a := aA) (b := aB) (by decide) (by decide))
    fun v ⟨hv, mv, v14, v15, v16, v17, m18, m19, m20, m21, v5, v6, z22, z23, z24, z25, kv⟩ => ?_
  rw [hU] at v14
  rw [hV] at v15
  rw [hQ] at v16
  rw [hR] at v17
  -- `m`'s pointer and `iv`.
  refine ptr_ok hv.ws (by decide) (by decide) (by decide) (by decide) ?_
  have hv1 := hv.of_keep' (Keep.write v .r7 (off B (arr w aMz)))
  refine ldW_ok hv1 (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  simp only [mem_write]
  generalize hv2 : (v.write .r7 (off B (arr w aMz))).write .r4 (v.mem.readW (off B (arr w aW + wIv)) 64) = v2
  have kv2 : Keep [.r7, .r4] v v2 := by rw [← hv2]; exact ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono
  have hv2' := hv.of_keep' kv2
  have mv2 : v2.mem = s.mem := by rw [← hv2]; simp only [mem_write, mv]
  have v2_7 : v2.gpr .r7 = off B (arr w aMz) := by rw [← hv2]; simp [gpr_write]
  have v2_4 : v2.gpr .r4 = s.mem.readW (off B (arr w aW + wIv)) 64 := by rw [← hv2]; simp [gpr_write, mv]
  have gv : ∀ r, r ∉ [Reg.r7, .r4] → v2.gpr r = v.gpr r := fun r hr => kv2.gpr _ hr
  rw [WP.block_append_iff]
  -- Word 0.
  refine WP.mono (abFirst_ok (dA := arr w aA) (dB := arr w aB) (dM := arr w aMz) hv2'.ws.scr (by rw [gv _ (by decide)]; exact v5) (by rw [gv _ (by decide)]; exact v6)
    v2_7 (by omega) (by omega) (by omega)
    (by rw [gv _ (by decide), m18, gv _ (by decide)]) (by rw [gv _ (by decide), m19, gv _ (by decide)])
    (by rw [gv _ (by decide), m20, gv _ (by decide)]) (by rw [gv _ (by decide), m21, gv _ (by decide)]))
    fun x ⟨⟨x28, x12, x22, x23, x9, x24, x25, x11, xm⟩, kx⟩ => ?_
  have hx := hv2'.of_keep' kx
  rw [WP.block_append_iff]
  refine WP.mono (cntN_ok hx) fun x' ⟨⟨x8, xm'⟩, kx'⟩ => ?_
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = BitVec.ofNat 64 k ∧ t.mem = x'.mem) ?_ (by decide))
    fun y ⟨⟨y8, ym⟩, ky⟩ => ?_
  · prun [x8, hkν]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hy := (hx.of_keep' kx').of_keep' ky
  have g : ∀ r, r ∉ [Reg.r0, .r3, .r4, .r9, .r11, .r12, .r22, .r23, .r24, .r25, .r26, .r27, .r28] → r ≠ .r8 →
      y.gpr r = v2.gpr r :=
    fun r h1 h2 => (ky.gpr _ (by simp [h2])).trans ((kx'.gpr _ (by simp [h2])).trans (kx.gpr _ h1))
  have kyr : ∀ r, r ≠ .r8 → y.gpr r = x.gpr r := fun r hr => (ky.gpr _ (by simp [hr])).trans (kx'.gpr _ (by simp [hr]))
  have y14 : y.gpr .r14 = BitVec.ofInt 64 (mat I).u := by rw [g .r14 (by decide) (by decide), gv _ (by decide)]; exact v14
  have y15 : y.gpr .r15 = BitVec.ofInt 64 (mat I).v := by rw [g .r15 (by decide) (by decide), gv _ (by decide)]; exact v15
  have y16 : y.gpr .r16 = BitVec.ofInt 64 (mat I).q := by rw [g .r16 (by decide) (by decide), gv _ (by decide)]; exact v16
  have y17 : y.gpr .r17 = BitVec.ofInt 64 (mat I).r := by rw [g .r17 (by decide) (by decide), gv _ (by decide)]; exact v17
  have em : y.mem = s.mem := ym.trans (xm'.trans (xm.trans mv2))
  have wv1 : ∀ d, wordsVal y.mem B d 1 = (word s.mem B d).toNat := fun d => by rw [em]; simp [wordsVal]
  have e0 : wordsVal s.mem B (arr w aMz) (nu n) % 2 ^ 64 = (word s.mem B (arr w aMz)).toNat := by
    rw [hkν]
    show ((word s.mem B (arr w aMz)).toNat + 2 ^ 64 * wordsVal s.mem B (arr w aMz + 8) k) % 2 ^ 64 = _
    have := (word s.mem B (arr w aMz)).isLt; omega
  have hm0 : ((word s.mem B (arr w aMz)).toNat * (v2.gpr .r4).toNat + 1) % 2 ^ 64 = 0 := by
    rw [v2_4, hiv, ← e0, hP, Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]; exact hm
  have xw : ∀ d, word v2.mem B d = word s.mem B d := fun d => by rw [mv2]
  refine ⟨_, _, ((((kv.trans kv2).trans kx).trans kx').trans ky).mono (by decide), em, hy,
    by rw [g .r5 (by decide) (by decide), gv _ (by decide)]; exact v5,
    by rw [g .r6 (by decide) (by decide), gv _ (by decide)]; exact v6,
    by rw [g .r7 (by decide) (by decide)]; exact v2_7, y8, y14, y15, y16, y17,
    by rw [g .r18 (by decide) (by decide), gv _ (by decide), m18, ← gv .r14 (by decide), ← g .r14 (by decide) (by decide)],
    by rw [g .r19 (by decide) (by decide), gv _ (by decide), m19, ← gv .r15 (by decide), ← g .r15 (by decide) (by decide)],
    by rw [g .r20 (by decide) (by decide), gv _ (by decide), m20, ← gv .r16 (by decide), ← g .r16 (by decide) (by decide)],
    by rw [g .r21 (by decide) (by decide), gv _ (by decide), m21, ← gv .r17 (by decide), ← g .r17 (by decide) (by decide)],
    by rw [kyr .r28 (by decide), x28, BitVec.toNat_mul, v2_4, hiv],
    by rw [kyr .r12 (by decide), x12, BitVec.toNat_mul, v2_4, hiv], ?_, ?_⟩
  · rw [wv1, wv1, wv1, kyr .r28 (by decide), x28, kyr .r22 (by decide), x22, kyr .r23 (by decide), x23,
      kyr .r9 (by decide), x9, g .r14 (by decide) (by decide), g .r15 (by decide) (by decide), xw, xw, xw]
    rw [xw, xw] at *
    exact ab_init _ _ _ _ _ _ _ _ _ (by rw [gv _ (by decide)]; exact z22) (by rw [gv _ (by decide)]; exact z23)
      rfl (by rw [gv _ (by decide), v14, tu]; omega) (by rw [gv _ (by decide), v14, tu]; omega)
      (by rw [gv _ (by decide), v15, tv]; omega) (by rw [gv _ (by decide), v15, tv]; omega) hm0
  · rw [wv1, wv1, wv1, kyr .r12 (by decide), x12, kyr .r24 (by decide), x24, kyr .r25 (by decide), x25,
      kyr .r11 (by decide), x11, g .r16 (by decide) (by decide), g .r17 (by decide) (by decide), xw, xw, xw]
    rw [xw, xw] at *
    exact ab_init _ _ _ _ _ _ _ _ _ (by rw [gv _ (by decide)]; exact z24) (by rw [gv _ (by decide)]; exact z25)
      rfl (by rw [gv _ (by decide), v16, tq]; omega) (by rw [gv _ (by decide), v16, tq]; omega)
      (by rw [gv _ (by decide), v17, tr]; omega) (by rw [gv _ (by decide), v17, tr]; omega) hm0

/-- The rest of `updateAB`, from `updateAB_head`'s state: words `1 … ν - 1`
and word `ν`. -/
theorem updateAB_tail [Divstep.TcSLaw] {s y : State} {B : Addr} {Z w N n c p iv k w1 w2 : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n c) (hN : N ≤ 256) (hkν : nu n = k + 1)
    (hA : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.a % 2 ^ (64 * (nu n + 1)))
    (hB : (wordsVal s.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.b % 2 ^ (64 * (nu n + 1)))
    (hP : wordsVal s.mem B (arr w aMz) (nu n) = p)
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) (hb : -(p : Int) < I.b ∧ I.b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * nu n)) (hm : (p * iv + 1) % 2 ^ 64 = 0)
    (ksy : Keep bRegs s y) (emy : y.mem = s.mem) (hy : Ctx y B Z w N n c)
    (y5 : y.gpr .r5 = off B (arr w aA)) (y6 : y.gpr .r6 = off B (arr w aB)) (y7 : y.gpr .r7 = off B (arr w aMz))
    (y8 : y.gpr .r8 = BitVec.ofNat 64 k)
    (y14 : y.gpr .r14 = BitVec.ofInt 64 (mat I).u) (y15 : y.gpr .r15 = BitVec.ofInt 64 (mat I).v)
    (y16 : y.gpr .r16 = BitVec.ofInt 64 (mat I).q) (y17 : y.gpr .r17 = BitVec.ofInt 64 (mat I).r)
    (y18 : y.gpr .r18 = sgn (y.gpr .r14)) (y19 : y.gpr .r19 = sgn (y.gpr .r15))
    (y20 : y.gpr .r20 = sgn (y.gpr .r16)) (y21 : y.gpr .r21 = sgn (y.gpr .r17))
    (ka : (y.gpr .r28).toNat = w1 * iv % 2 ^ 64) (kb : (y.gpr .r12).toNat = w2 * iv % 2 ^ 64)
    (i1 : ABAcc (y.gpr .r14).toInt (y.gpr .r15).toInt (y.gpr .r28).toNat w1 (wordsVal y.mem B (arr w aA) 1)
      (wordsVal y.mem B (arr w aB) 1) (wordsVal y.mem B (arr w aMz) 1) 0 0 (y.gpr .r22) (y.gpr .r23) (y.gpr .r9))
    (i2 : ABAcc (y.gpr .r16).toInt (y.gpr .r17).toInt (y.gpr .r12).toNat w2 (wordsVal y.mem B (arr w aA) 1)
      (wordsVal y.mem B (arr w aB) 1) (wordsVal y.mem B (arr w aMz) 1) 0 0 (y.gpr .r24) (y.gpr .r25) (y.gpr .r11)) :
    WP isa (.seq (.ite (.zero .d .r8) (.block []) (countLoop .r8 abBody)) (.block abLast)) y fun t =>
      Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aA, aB] [] s.mem t.mem ∧
      (wordsVal t.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        Divstep.mredRaw p iv ((mat I).u * I.a + (mat I).v * I.b) % 2 ^ (64 * (nu n + 1)) ∧
      (wordsVal t.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        Divstep.mredRaw p iv ((mat I).q * I.a + (mat I).r * I.b) % 2 ^ (64 * (nu n + 1)) ∧
      Keep bRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.wbig
  have := h.ws.wle
  have hnw := h.ws.nowrap
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd I.d I.f I.g 59
  have ha2 : |I.a| ≤ 2 * p := abs_le.mpr ⟨by omega, by omega⟩
  have hb2 : |I.b| ≤ 2 * p := abs_le.mpr ⟨by omega, by omega⟩
  have ht₁ := Divstep.TcSLaw.comb_le2 (by norm_num) (by exact_mod_cast hp) bu ha2 hb2
  have ht₂ := Divstep.TcSLaw.comb_le2 (by norm_num) (by exact_mod_cast hp) bq ha2 hb2
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have nM : aMz < N := by unfold aMz; omega
  have fA := h.ws.arr_fit nA
  have fB := h.ws.arr_fit nB
  have fM := h.ws.arr_fit nM
  have eAB : arr w aA + S w ≤ arr w aB := KeyWorkspace.arr_end (by decide)
  have eMA : arr w aMz + S w ≤ arr w aA := KeyWorkspace.arr_end (by decide)
  have u1 := (natAbs61 bu).1
  have u2 := (natAbs61 bu).2
  have q1 := (natAbs61 bq).1
  have q2 := (natAbs61 bq).2
  have tu := toInt_mat u1
  have tv := toInt_mat u2
  have tq := toInt_mat q1
  have tr := toInt_mat q2
  have sepA : arr w aA + 8 * (k + 1) + 8 ≤ arr w aB ∨ arr w aB + 8 * k ≤ arr w aA + 8 * (k + 1) := .inl (by omega)
  have sepB : arr w aB + 8 * (k + 1) + 8 ≤ arr w aA ∨ arr w aA + 8 * k ≤ arr w aB + 8 * (k + 1) := .inr (by omega)
  have fitA : arr w aA + 8 * (k + 1) + 8 ≤ 2 ^ 64 := by omega
  have fitB : arr w aB + 8 * (k + 1) + 8 ≤ 2 ^ 64 := by omega
  have ixA : arr w aA + 8 * k + 8 = arr w aA + 8 * (k + 1) := by omega
  have ixB : arr w aB + 8 * k + 8 = arr w aB + 8 * (k + 1) := by omega
  rw [WP.seq_iff]
  -- Words `1 … ν - 1`.
  refine WP.mono (abLoop?_ok (n := k) hy.ws.scr y5 y6 y7 y8 (by omega) (by omega) (by omega) (by omega)
    (.inl (by omega)) (.inr (by omega)) (.inr (by omega)) y18 y19 y20 y21
    (by rw [y14, tu]; omega) (by rw [y14, tu]; omega) (by rw [y15, tv]; omega) (by rw [y15, tv]; omega)
    (by rw [y16, tq]; omega) (by rw [y16, tq]; omega) (by rw [y17, tr]; omega) (by rw [y17, tr]; omega)
    i1 i2) fun z ⟨za, zb, z5, z6, z7, zout, kz⟩ => ?_
  have hz := hy.of_keep' kz
  have gz : ∀ r, r ∉ abRegs → z.gpr r = y.gpr r := fun r hr => kz.gpr _ hr
  -- Word `ν`.
  refine WP.mono (abLast_ok hz.ws.scr z5 z6 (by omega) (by omega)
    (by rw [gz .r18 (by decide), gz .r14 (by decide)]; exact y18)
    (by rw [gz .r19 (by decide), gz .r15 (by decide)]; exact y19)
    (by rw [gz .r20 (by decide), gz .r16 (by decide)]; exact y20)
    (by rw [gz .r21 (by decide), gz .r17 (by decide)]; exact y21)) fun t1 ⟨m1, k1⟩ => ?_
  -- The frame.
  have Kz : KeyWorkspace.Keep B w [aA, aB] [] y.mem z.mem :=
    Outs.cover zout fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(arr w aA, S w), by simp [KeyWorkspace.ranges], by simp, by simp; omega⟩
      · exact ⟨(arr w aB, S w), by simp [KeyWorkspace.ranges], by simp, by simp; omega⟩
  have K1 : KeyWorkspace.Keep B w [aA, aB] [] z.mem t1.mem := by
    rw [m1]
    exact (((KeyWorkspace.Keep.of_arr (o := aA) (d := 8 * k) (writeW_outside _ B _ (by omega)) (by omega)
      (by simp)).trans
      (KeyWorkspace.Keep.of_arr (o := aA) (d := 8 * k + 8) (writeW_outside _ B _ (by omega)) (by omega)
        (by simp))).trans
      (KeyWorkspace.Keep.of_arr (o := aB) (d := 8 * k) (writeW_outside _ B _ (by omega)) (by omega) (by simp))).trans
      (KeyWorkspace.Keep.of_arr (o := aB) (d := 8 * k + 8) (writeW_outside _ B _ (by omega)) (by omega) (by simp))
  have kk : Keep bRegs s t1 := ((ksy.trans kz).trans k1).mono (by decide)
  -- The values.
  have rdA : word z.mem B (arr w aA + 8 * k + 8) = word y.mem B (arr w aA + 8 * (k + 1)) := by
    rw [ixA]; exact outs2_word (d := arr w aA) (e := arr w aB) (j := k) (i := k + 1) zout (Nat.le_succ k) sepA fitA
  have rdB : word z.mem B (arr w aB + 8 * k + 8) = word y.mem B (arr w aB + 8 * (k + 1)) := by
    rw [ixB]; exact outs2_word' (d := arr w aA) (e := arr w aB) (j := k) (i := k + 1) zout (Nat.le_succ k) sepB fitB
  have DA : wordsVal y.mem B (arr w aA) (k + 1) + 2 ^ (64 * (k + 1)) * (word z.mem B (arr w aA + 8 * k + 8)).toNat =
      wordsVal s.mem B (arr w aA) (nu n + 1) := by
    rw [rdA, ← wordsVal_succ_top, emy, hkν]
  have DB : wordsVal y.mem B (arr w aB) (k + 1) + 2 ^ (64 * (k + 1)) * (word z.mem B (arr w aB + 8 * k + 8)).toNat =
      wordsVal s.mem B (arr w aB) (nu n + 1) := by
    rw [rdB, ← wordsVal_succ_top, emy, hkν]
  have eP' : wordsVal y.mem B (arr w aMz) (k + 1) = p := by rw [emy, ← hkν]; exact hP
  have hpA' : p < 2 ^ (64 * (k + 1)) := hkν ▸ hpA
  have hA' : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (k + 1 + 1)) = I.a % 2 ^ (64 * (k + 1 + 1)) :=
    hkν ▸ hA
  have hB' : (wordsVal s.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (k + 1 + 1)) = I.b % 2 ^ (64 * (k + 1 + 1)) :=
    hkν ▸ hB
  refine ⟨h.of_keep' kk, by rw [← emy]; exact Kz.trans K1, ?_, ?_, kk⟩
  all_goals rw [m1, gz .r14 (by decide), gz .r15 (by decide), gz .r16 (by decide), gz .r17 (by decide), hkν]
  · rw [wv_apart2 _ _ _ _ (by omega) (by omega) (by omega), wv_top2 _ _ _ _ _ _ (by omega)]
    exact ab_mred (by rw [y14, tu]) (by rw [y15, tv]) u1 u2 za (wordsVal_lt _ _ _ _) DA DB hA' hB'
      ka eP' hp hpA' hm ht₁
  · rw [wv_top2 _ _ _ _ _ _ (by omega), wv_apart2 _ _ _ _ (by omega) (by omega) (by omega)]
    exact ab_mred (by rw [y16, tq]) (by rw [y17, tr]) q1 q2 zb (wordsVal_lt _ _ _ _) DA DB hA' hB'
      kb eP' hp hpA' hm ht₂

/-- `updateAB`: the new `a` and `b` from the matrix in the window, in place. -/
theorem updateAB_ok [Divstep.TcSLaw] {s : State} {B : Addr} {Z w N n c p iv : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hA : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.a % 2 ^ (64 * (nu n + 1)))
    (hB : (wordsVal s.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.b % 2 ^ (64 * (nu n + 1)))
    (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) (hP : wordsVal s.mem B (arr w aMz) (nu n) = p)
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat I).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat I).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat I).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat I).r)
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) (hb : -(p : Int) < I.b ∧ I.b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * nu n)) (hm : (p * iv + 1) % 2 ^ 64 = 0) :
    WP isa updateAB s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aA, aB] [] s.mem t.mem ∧
      (wordsVal t.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        Divstep.mredRaw p iv ((mat I).u * I.a + (mat I).v * I.b) % 2 ^ (64 * (nu n + 1)) ∧
      (wordsVal t.mem B (arr w aB) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) =
        Divstep.mredRaw p iv ((mat I).q * I.a + (mat I).r * I.b) % 2 ^ (64 * (nu n + 1)) ∧
      Keep bRegs s t := by
  obtain ⟨k, hkν⟩ : ∃ k, nu n = k + 1 := ⟨nu n - 1, by have := h.nu1; omega⟩
  simp only [updateAB, seqs]
  rw [WP.seq_iff]
  exact WP.mono (updateAB_head h hN hkν hiv hP hU hV hQ hR hm)
    fun y ⟨_, _, ksy, emy, hy, y5, y6, y7, y8, y14, y15, y16, y17, y18, y19, y20, y21, ka, kb, i1, i2⟩ =>
      updateAB_tail h hN hkν hA hB hP ha hb hp hpA hm ksy emy hy y5 y6 y7 y8 y14 y15 y16 y17 y18 y19 y20 y21
        ka kb i1 i2

theorem batchS_eq (p iv : Int) (I : Divstep.IState) : Divstep.batchS 59 p iv I =
    ⟨(mat I).d, ((mat I).u * I.f + (mat I).v * I.g) / 2 ^ 59, ((mat I).q * I.f + (mat I).r * I.g) / 2 ^ 59,
      Divstep.mredRaw p iv ((mat I).u * I.a + (mat I).v * I.b),
      Divstep.mredRaw p iv ((mat I).q * I.a + (mat I).r * I.b)⟩ := rfl

/-! ## A batch -/

theorem dec_eq {n c : Nat} (hn : n < 2 ^ 15) (hc : c < 2 ^ 40) :
    BitVec.ofNat 64 (n + 32768 * (c + 1)) - BitVec.ofNat 64 32768 = BitVec.ofNat 64 (n + 32768 * c) ∧
      (BitVec.ofNat 64 (n + 32768 * c) >>> 15).toNat = c := by
  refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
  · rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

/-- `countDown`: the count of the batches left, `c`, in `r10`, and whether it
is zero in `r3`. -/
theorem countDown_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n (c + 1)) :
    WP isa (.block countDown) t fun u => (Ctx u B Z w N n c ∧ ((u.gpr .r3).toNat ≠ 0 ↔ c ≠ 0) ∧ u.mem = t.mem) ∧
      Keep [.r3, .r10] t u := by
  refine WP.mono (WP.keep [.r3, .r10] (Q := fun u => u.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * c) ∧
      (u.gpr .r3).toNat = c ∧ u.mem = t.mem) ?_ (by decide)) fun u ⟨⟨r10, r3, m⟩, k⟩ =>
    ⟨⟨⟨h.ws.of_keep k, r10, h.npos, h.nw, h.room, by have := h.cb; omega, h.wbig, h.fit⟩, by rw [r3], m⟩, k⟩
  have e := dec_eq (c := c) h.nlt (by have := h.cb; omega)
  prun [countDown, h.r10]
  rw [e.1]
  exact ⟨rfl, e.2⟩

/-- A batch: `Divstep.batchS 59`, and the count of the batches left, `c`, in
`r10` and whether it is zero in `r3`. -/
theorem batch_ok [Divstep.TcSLaw] {s : State} {B : Addr} {Z w N n c p iv : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n (c + 1)) (hst : BS s B w n p iv I)
    (hN : N ≤ 256) (hd : |I.d| + 2 * 59 < 2 ^ 62) (hodd : I.f % 2 = 1)
    (hF : |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3)
    (ha : -(p : Int) < I.a ∧ I.a < 2 * p) (hb : -(p : Int) < I.b ∧ I.b < 2 * p)
    (hp : 0 < p) (hpA : p < 2 ^ (64 * nu n)) (hm : (p * iv + 1) % 2 ^ 64 = 0) :
    WP isa batch s fun t => Ctx t B Z w N n c ∧ BS t B w n p iv (Divstep.batchS 59 p iv I) ∧
      ((t.gpr .r3).toNat ≠ 0 ↔ c ≠ 0) ∧
      KeyWorkspace.Keep B w [aF, aG, aA, aB, aT1, aT2, aT3, aW] [] s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
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
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have n3 : aT3 < N := by unfold aT3; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  simp only [batch, seqs, update]
  rw [WP.seq_iff]
  refine WP.mono (head_ok h hst.toBG hN hd hodd) fun t1 ⟨h1, K1, out1, d1, u1, v1, q1, r1, k1⟩ => ?_
  have fW := fit _ nW
  have iv1 : (t1.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv := by
    rw [Outside.readW64 out1 (by unfold wIv; omega) (by unfold wIv; omega)]; exact hst.iv
  have kv1 : ∀ j, j ≠ aW → j < N → ∀ k, 8 * k ≤ S w → wordsVal t1.mem B (arr w j) k = wordsVal s.mem B (arr w j) k :=
    fun j hj hjN k hk => keep_wv K1 hk (by simp [Ne.symm hj]) (by simp) (fit _ hjN)
  rw [WP.seq_iff, WP.seq_iff]
  -- The borrowed registers kept.
  refine WP.mono (spill_ok h1) fun u ⟨ku, Ku, s1, s2, s3⟩ => ?_
  have hu := h1.of_keep' ku
  have wdu : ∀ o, o + 8 ≤ 48 → u.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => keep_word Ku (by omega) (by decide) (by simp) (fit _ nW)
  have kvu : ∀ j, j ≠ aT1 → j ≠ aT2 → j ≠ aT3 → j < N → ∀ k, 8 * k ≤ S w →
      wordsVal u.mem B (arr w j) k = wordsVal t1.mem B (arr w j) k :=
    fun j h1 h2 h3 hjN k hk => keep_wv Ku hk (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]) (by simp) (fit _ hjN)
  rw [WP.seq_iff]
  refine WP.mono (updateG_ok hu hN
    (by rw [kvu _ (by decide) (by decide) (by decide) nF _ hk, kv1 _ (by decide) nF _ hk]; exact hst.f)
    (by rw [kvu _ (by decide) (by decide) (by decide) nG _ hk, kv1 _ (by decide) nG _ hk]; exact hst.g)
    (by rw [wdu _ (by decide)]; exact u1) (by rw [wdu _ (by decide)]; exact v1)
    (by rw [wdu _ (by decide)]; exact q1) (by rw [wdu _ (by decide)]; exact r1) hodd hF hG)
    fun t2 ⟨h2, K2, ef, eg, k2⟩ => ?_
  have wd2 : ∀ o, o + 8 ≤ 48 → t2.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => (keep_word K2 (by omega) (by decide) (by simp) (fit _ nW)).trans (wdu o ho)
  have kv2 : ∀ j, j ≠ aF → j ≠ aG → j < N → ∀ k, 8 * k ≤ S w →
      wordsVal t2.mem B (arr w j) k = wordsVal u.mem B (arr w j) k :=
    fun j h1 h2 hjN k hk => keep_wv K2 hk (by simp [Ne.symm h1, Ne.symm h2]) (by simp) (fit _ hjN)
  rw [WP.seq_iff]
  refine WP.mono (updateAB_ok h2 hN
    (by rw [kv2 _ (by decide) (by decide) nA _ hk, kvu _ (by decide) (by decide) (by decide) nA _ hk,
      kv1 _ (by decide) nA _ hk]; exact hst.a)
    (by rw [kv2 _ (by decide) (by decide) nB _ hk, kvu _ (by decide) (by decide) (by decide) nB _ hk,
      kv1 _ (by decide) nB _ hk]; exact hst.b)
    (by rw [wd2 _ (by decide)]; exact iv1)
    (by rw [kv2 _ (by decide) (by decide) nM _ hk0, kvu _ (by decide) (by decide) (by decide) nM _ hk0,
      kv1 _ (by decide) nM _ hk0]; exact hst.P)
    (by rw [wd2 _ (by decide)]; exact u1) (by rw [wd2 _ (by decide)]; exact v1)
    (by rw [wd2 _ (by decide)]; exact q1) (by rw [wd2 _ (by decide)]; exact r1)
    ha hb hp hpA hm) fun t3 ⟨h3, K3, ea, eb, k3⟩ => ?_
  have wd3 : ∀ o, o + 8 ≤ 48 → t3.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => (keep_word K3 (by omega) (by decide) (by simp) (fit _ nW)).trans (wd2 o ho)
  have kv3 : ∀ j, j ≠ aA → j ≠ aB → j < N → ∀ k, 8 * k ≤ S w →
      wordsVal t3.mem B (arr w j) k = wordsVal t2.mem B (arr w j) k :=
    fun j h1 h2 hjN k hk => keep_wv K3 hk (by simp [Ne.symm h1, Ne.symm h2]) (by simp) (fit _ hjN)
  -- The borrowed registers back.
  refine WP.mono (restore_ok h3) fun t4 ⟨k4, m4, l1, l2, l3⟩ => ?_
  have K23 : KeyWorkspace.Keep B w [aF, aG, aA, aB] [] u.mem t3.mem := KeyWorkspace.Keep.join K2 K3
  have wd : ∀ j, j ≠ aF → j ≠ aG → j ≠ aA → j ≠ aB → j < N → ∀ i < 6,
      word t3.mem B (arr w j + 8 * i) = word u.mem B (arr w j + 8 * i) := fun j h1 h2 h3 h4 hj i hi =>
    keep_word K23 (o := 8 * i) (b := 64) (by omega)
      (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]) (by simp) (fit _ hj)
  have kb : Keep (.r3 :: kRegs) t1 t4 := spill_restore ku s1 s2 s3 (k2.trans' k3)
    (wd _ (by decide) (by decide) (by decide) (by decide) n1) (wd _ (by decide) (by decide) (by decide) (by decide) n2)
    (fun i hi => wd _ (by decide) (by decide) (by decide) (by decide) n3 i (by omega)) k4 l1 l2 l3
  have h4 := h1.of_keep' kb
  refine WP.mono (countDown_ok h4) fun t5 ⟨⟨h5, r3, m5⟩, k5⟩ => ?_
  have k : Keep (.r10 :: kRegs) s t5 :=
    ((k1.trans' (kb.mono (by decide))).mono (by decide)).trans' (k5.mono (by decide))
  have em : t5.mem = t3.mem := m5.trans m4
  rw [batchS_eq]
  refine ⟨h5, ⟨⟨?_, ?_, ?_⟩, by rw [em]; exact ea, by rw [em]; exact eb, ?_, ?_, ?_⟩, r3,
    by rw [em]; exact ((K1.mono (by simp)).trans (Ku.mono (by simp))).trans (K23.mono (by simp)), k⟩
  · rw [em, wd3 _ (by decide)]; dsimp only; exact d1
  · rw [em, kv3 _ (by decide) (by decide) nF _ hk]; exact ef
  · rw [em, kv3 _ (by decide) (by decide) nG _ hk]; exact eg
  · rw [em, wd3 _ (by decide)]; exact iv1
  · rw [em, kv3 _ (by decide) (by decide) nM _ hk0, kv2 _ (by decide) (by decide) nM _ hk0,
      kvu _ (by decide) (by decide) (by decide) nM _ hk0, kv1 _ (by decide) nM _ hk0]
    exact hst.P
  · rw [em, kv3 _ (by decide) (by decide) nM _ hk, kv2 _ (by decide) (by decide) nM _ hk,
      kvu _ (by decide) (by decide) (by decide) nM _ hk, kv1 _ (by decide) nM _ hk]
    exact hst.P1

/-- A batch of `f` and `g` alone: the next `d`, `f` and `g`, and the count of the batches left, `c`, in
`r10` and whether it is zero in `r3`. -/
theorem batchG_ok {s : State} {B : Addr} {Z w N n c p iv : Nat} {I : Divstep.IState}
    (h : Ctx s B Z w N n (c + 1)) (hst : BG s B w n I)
    (hN : N ≤ 256) (hd : |I.d| + 2 * 59 < 2 ^ 62) (hodd : I.f % 2 = 1)
    (hF : |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3) (hG : |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3) :
    WP isa batchG s fun t => Ctx t B Z w N n c ∧ BG t B w n (Divstep.batchS 59 p iv I) ∧
      ((t.gpr .r3).toNat ≠ 0 ↔ c ≠ 0) ∧
      KeyWorkspace.Keep B w [aF, aG, aT1, aT2, aT3, aW] [] s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wbig
  have := h.nuw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have n3 : aT3 < N := by unfold aT3; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  simp only [batchG, seqs, updateGS]
  rw [WP.seq_iff]
  refine WP.mono (head_ok h hst hN hd hodd) fun t1 ⟨h1, K1, out1, d1, u1, v1, q1, r1, k1⟩ => ?_
  have fW := fit _ nW
  have kv1 : ∀ j, j ≠ aW → j < N → ∀ k, 8 * k ≤ S w → wordsVal t1.mem B (arr w j) k = wordsVal s.mem B (arr w j) k :=
    fun j hj hjN k hk => keep_wv K1 hk (by simp [Ne.symm hj]) (by simp) (fit _ hjN)
  rw [WP.seq_iff, WP.seq_iff]
  -- The borrowed registers kept.
  refine WP.mono (spill_ok h1) fun u ⟨ku, Ku, s1, s2, s3⟩ => ?_
  have hu := h1.of_keep' ku
  have wdu : ∀ o, o + 8 ≤ 48 → u.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => keep_word Ku (by omega) (by decide) (by simp) (fit _ nW)
  have kvu : ∀ j, j ≠ aT1 → j ≠ aT2 → j ≠ aT3 → j < N → ∀ k, 8 * k ≤ S w →
      wordsVal u.mem B (arr w j) k = wordsVal t1.mem B (arr w j) k :=
    fun j h1 h2 h3 hjN k hk => keep_wv Ku hk (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]) (by simp) (fit _ hjN)
  rw [WP.seq_iff]
  refine WP.mono (updateG_ok hu hN
    (by rw [kvu _ (by decide) (by decide) (by decide) nF _ hk, kv1 _ (by decide) nF _ hk]; exact hst.f)
    (by rw [kvu _ (by decide) (by decide) (by decide) nG _ hk, kv1 _ (by decide) nG _ hk]; exact hst.g)
    (by rw [wdu _ (by decide)]; exact u1) (by rw [wdu _ (by decide)]; exact v1)
    (by rw [wdu _ (by decide)]; exact q1) (by rw [wdu _ (by decide)]; exact r1) hodd hF hG)
    fun t2 ⟨h2, K2, ef, eg, k2⟩ => ?_
  have wd2 : ∀ o, o + 8 ≤ 48 → t2.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => (keep_word K2 (by omega) (by decide) (by simp) (fit _ nW)).trans (wdu o ho)
  -- The borrowed registers back.
  refine WP.mono (restore_ok h2) fun t4 ⟨k4, m4, l1, l2, l3⟩ => ?_
  have wd : ∀ j, j ≠ aF → j ≠ aG → j < N → ∀ i < 6,
      word t2.mem B (arr w j + 8 * i) = word u.mem B (arr w j + 8 * i) := fun j h1 h2 hj i hi =>
    keep_word K2 (o := 8 * i) (b := 64) (by omega) (by simp [Ne.symm h1, Ne.symm h2]) (by simp) (fit _ hj)
  have kb : Keep (.r3 :: kRegs) t1 t4 := spill_restore ku s1 s2 s3 k2
    (wd _ (by decide) (by decide) n1) (wd _ (by decide) (by decide) n2)
    (fun i hi => wd _ (by decide) (by decide) n3 i (by omega)) k4 l1 l2 l3
  have h4 := h1.of_keep' kb
  refine WP.mono (countDown_ok h4) fun t5 ⟨⟨h5, r3, m5⟩, k5⟩ => ?_
  have k : Keep (.r10 :: kRegs) s t5 :=
    ((k1.trans' (kb.mono (by decide))).mono (by decide)).trans' (k5.mono (by decide))
  have em : t5.mem = t2.mem := m5.trans m4
  rw [batchS_eq]
  refine ⟨h5, ⟨?_, by rw [em]; exact ef, by rw [em]; exact eg⟩, r3,
    by rw [em]; exact ((K1.mono (by simp)).trans (Ku.mono (by simp))).trans (K2.mono (by simp)), k⟩
  rw [em, wd2 _ (by decide)]; dsimp only; exact d1

end VG.Proof.Rsa.PPC64LE.InvBatch


namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S)
open VG.Proof.Rsa.Divstep (oddInput)

/-- The bounds of a batch from the run's (`Divstep.TcSLaw.invRunS_bounds`, `M = 2^(64 ν + 1)`). -/
theorem run_bounds [Divstep.TcSLaw] {n p iv x k : Nat} (odd : p % 2 = 1) (hinv : (p * iv + 1) % 2 ^ 64 = 0)
    (pc : p < 2 ^ (64 * nu n)) (xc : x < 2 * 2 ^ (64 * nu n)) :
    let I := Divstep.invRunS 59 p iv x k
    |I.d| ≤ 1 + 2 * (59 * k : Nat) ∧ I.f % 2 = 1 ∧ |I.f| ≤ 2 ^ (64 * nu n) * 2 ^ 3 ∧
      |I.g| ≤ 2 ^ (64 * nu n) * 2 ^ 3 ∧ (-(p : Int) < I.a ∧ I.a < 2 * p) ∧ (-(p : Int) < I.b ∧ I.b < 2 * p) := by
  intro I
  have hmI : ((p : Int) * (iv : Int) + 1) % 2 ^ 64 = 0 := by exact_mod_cast hinv
  have hM8 : (2 * 2 ^ (64 * nu n) : Int) ≤ 2 ^ (64 * nu n) * 2 ^ 3 := by
    have : 2 * 2 ^ (64 * nu n) ≤ 2 ^ (64 * nu n) * 2 ^ 3 := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by decide)
    exact_mod_cast this
  obtain ⟨bd, bf1, bf, bg, ba0, ba1, bb0, bb1⟩ := Divstep.TcSLaw.invRunS_bounds (N := 59) (by decide) (p := p) (m := iv)
    (x := x) (M := 2 * 2 ^ (64 * nu n)) (by exact_mod_cast odd) (by omega) hmI (Int.natCast_nonneg _)
    (by have : p ≤ 2 * 2 ^ (64 * nu n) := by omega
        exact_mod_cast this)
    (by have : x ≤ 2 * 2 ^ (64 * nu n) := by omega
        exact_mod_cast this) k
  exact ⟨bd, bf1, le_trans bf hM8, le_trans bg hM8, ⟨ba0, ba1⟩, ⟨bb0, bb1⟩⟩

/-- After `k` batches. -/
def LoopAt (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n (3 * nu n + 2 - k) ∧ BS t B w n p iv (Divstep.invRunS 59 p iv x k) ∧
    KeyWorkspace.Keep B w [aF, aG, aA, aB, aT1, aT2, aT3, aW] [] s₀.mem t.mem ∧ Keep (.r10 :: kRegs) s₀ t

theorem loop_ok [Divstep.TcSLaw] {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n (3 * nu n + 2)) (hst : BS s B w n p iv (Divstep.invRunS 59 p iv x 0))
    (odd : p % 2 = 1) (hp0 : 0 < p) (hinv : (p * iv + 1) % 2 ^ 64 = 0)
    (pc : p < 2 ^ (64 * nu n)) (xc : x < 2 * 2 ^ (64 * nu n)) :
    WP isa (.loop batch (.nonzero .d .r3)) s (LoopAt s B Z w N n p iv x (3 * nu n + 2)) := by
  have hn := h.nuw
  have hw := h.ws.wle
  refine count_loop (by omega) (LoopAt s B Z w N n p iv x) (fun k hk t ⟨Ht, It, Kt, kt⟩ => ?_)
    ⟨by simpa using h, hst, KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, ha, hb⟩ := run_bounds (k := k) odd hinv pc xc
  rw [show 3 * nu n + 2 - k = (3 * nu n + 2 - k - 1) + 1 by omega] at Ht
  refine WP.mono (batch_ok Ht It hN (by push_cast at bd ⊢; omega) fo fb gb ha hb hp0 pc hinv)
    fun u ⟨Hu, Iu, ru, Ku, ku⟩ => ?_
  rw [show 3 * nu n + 2 - k - 1 = 3 * nu n + 2 - (k + 1) by omega] at Hu
  exact ⟨⟨Hu, Iu, Kt.trans Ku, kt.trans' ku⟩, by rw [ru]; omega⟩

/-- After `k` batches of `f` and `g` alone. -/
def LoopGAt (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n (3 * nu n + 2 - k) ∧ BG t B w n (Divstep.invRunS 59 p iv x k) ∧
    KeyWorkspace.Keep B w [aF, aG, aT1, aT2, aT3, aW] [] s₀.mem t.mem ∧ Keep (.r10 :: kRegs) s₀ t

theorem loopG_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n (3 * nu n + 2)) (hst : BG s B w n (Divstep.invRunS 59 p iv x 0))
    (odd : p % 2 = 1) (hinv : (p * iv + 1) % 2 ^ 64 = 0)
    (pc : p < 2 ^ (64 * nu n)) (xc : x < 2 * 2 ^ (64 * nu n)) :
    WP isa (.loop batchG (.nonzero .d .r3)) s (LoopGAt s B Z w N n p iv x (3 * nu n + 2)) := by
  have hn := h.nuw
  have hw := h.ws.wle
  refine count_loop (by omega) (LoopGAt s B Z w N n p iv x) (fun k hk t ⟨Ht, It, Kt, kt⟩ => ?_)
    ⟨by simpa using h, hst, KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, -, -⟩ := run_bounds (k := k) odd hinv pc xc
  rw [show 3 * nu n + 2 - k = (3 * nu n + 2 - k - 1) + 1 by omega] at Ht
  refine WP.mono (batchG_ok (p := p) (iv := iv) Ht It hN (by push_cast at bd ⊢; omega) fo fb gb)
    fun u ⟨Hu, Iu, ru, Ku, ku⟩ => ?_
  rw [show 3 * nu n + 2 - k - 1 = 3 * nu n + 2 - (k + 1) by omega] at Hu
  exact ⟨⟨Hu, Iu, Kt.trans Ku, kt.trans' ku⟩, by rw [ru]; omega⟩

end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE: the end

`normalize_ok`: `a` into `[0, p)`, negated if `f < 0`; `doublings_ok`:
`a 2^(5 (3 ν + 2)) mod p`; `finishG_ok`, `finishY_ok`: `|f|` and `a` into
arrays 1 and 3, `w` digits each.
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (copyWLoop_ok)

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
  rw [← Divstep.WordArith.half_top _ (wordsVal_lt m B d k), ← wordsVal_succ_top]
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

/-- `[o] = [a] - [b]` with `b ≤ a`: the difference, no borrow. -/
theorem sub_val {T A V R : Nat} (c : Bool) (hT : T < R) (hVA : V ≤ A)
    (h : T + V = A + R * (1 - c.toNat)) : T = A - V := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;> omega

/-- `li r11 1`. -/
theorem one11_ok (s : State) :
    WP isa (.block [.li .r11 1]) s fun u => (u.gpr .r11 = 1#64 ∧ u.mem = s.mem) ∧ Keep [.r11] s u :=
  WP.keep _ (by prun; try rfl) (by decide)

/-- `normalize`: `a` (`(-p, 2p)`, two's complement) into `[0, p)`, negated
modulo `p` if `f < 0`. -/
theorem normalize_ok {s : State} {B : Addr} {Z w N n c p : Nat} {a f : Int} (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p) (hpA : p < 2 ^ (64 * nu n))
    (ha : (wordsVal s.mem B (arr w aA) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = a % 2 ^ (64 * (nu n + 1)))
    (ha1 : -(p : Int) < a) (ha2 : a < 2 * p)
    (hf : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = f % 2 ^ (64 * (nu n + 1)))
    (hf1 : -(p : Int) ≤ f) (hf2 : f ≤ p) :
    WP isa normalize s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aA, aT3, aT1] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w aA) (nu n + 1) < p ∧
      (wordsVal t.mem B (arr w aA) (nu n + 1) : Int) ≡ (if 0 ≤ f then 1 else -1) * a [ZMOD p] ∧
      Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have hk : 8 * (nu n + 1) ≤ S w := by omega
  have hAp : (p : Int) < 2 ^ (64 * nu n) := by exact_mod_cast hpA
  obtain ⟨vA, sA⟩ := sign_word ha (by omega) (by omega)
  obtain ⟨-, sF⟩ := sign_word hf (by omega) (by omega)
  have hQA : 2 ^ (64 * (nu n + 1)) = 2 ^ (64 * nu n) * 2 ^ 64 := pow_succ64 _
  have hQ2 : 2 * 2 ^ (64 * nu n) ≤ 2 ^ (64 * (nu n + 1)) := by rw [hQA]; omega
  have hQI : ((2 ^ (64 * (nu n + 1)) : Nat) : Int) = 2 ^ (64 * (nu n + 1)) := by push_cast; rfl
  simp only [normalize, VG.Impl.Rsa.PPC64LE.InvBatch.reduce, seqs]
  -- `r11 := 1`.
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (one11_ok s) fun t1 ⟨⟨r5, m1⟩, k1⟩ => ?_
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
  rw [keep_wv K2 hk (by decide) (by simp) (fit _ nA), T2, wt2] at v3
  -- `[aA] = a mod p`.
  refine WP.mono (csub_ok (p := p) h3 nA nA n1 hN (by decide) (by decide) (by decide)
    (by rw [keep_wv K3 hk (by decide) (by simp) (fit _ nM), keep_wv K2 hk (by decide) (by simp) (fit _ nM), hp]) v3)
    fun t4 ⟨h4, K4, v4, k4⟩ => ?_
  -- `[aT3] = p - a`.
  rw [WP.seq_iff]
  refine WP.mono (subW_ok h4 n3 nM nA hN) fun t6 ⟨h6, K6, v6, k6⟩ => ?_
  rw [keep_wv K4 hk (by decide) (by simp) (fit _ nM), keep_wv K3 hk (by decide) (by simp) (fit _ nM),
    keep_wv K2 hk (by decide) (by simp) (fit _ nM), hp] at v6
  -- `[aA] = f < 0 ? p - a : a`.
  rw [WP.seq_iff]
  refine WP.mono (signSel_ok h6 nF nA nA n3 hN (by decide)) fun t7 ⟨h7, K7, v7, _, k7⟩ => ?_
  have K26 : KeyWorkspace.Keep B w [aT3, aA, aT1] [] s.mem t6.mem :=
    ((K2.mono (by simp)).trans (K3.mono (by simp))).trans ((K4.mono (by simp)).trans (K6.mono (by simp)))
  have wF : word t6.mem B (arr w aF + 8 * nu n) = word s.mem B (arr w aF + 8 * nu n) :=
    keep_word K26 (o := 8 * nu n) (b := 64) (by omega) (by decide) (by simp) (fit _ nF)
  rw [wF, keep_wv K6 hk (by decide) (by simp) (fit _ nA)] at v7
  refine WP.mono (csub_ok (p := p) h7 nA nA n1 hN (by decide) (by decide) (by decide)
    (by rw [keep_wv K7 hk (by decide) (by simp) (fit _ nM), keep_wv K26 hk (by decide) (by simp) (fit _ nM), hp]) v7)
    fun t8 ⟨h8, K8, v8, k8⟩ => ?_
  have k : Keep kRegs s t8 :=
    ((((((k1.mono (by decide)).trans' k2).trans' k3).trans' k4).trans' k6).trans' k7).trans' k8
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
  have T6 : wordsVal t6.mem B (arr w aT3) (nu n + 1) = p - wordsVal t4.mem B (arr w aA) (nu n + 1) :=
    sub_val t6.ca (wordsVal_lt _ _ _ _) (by omega) v6
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
theorem double_ok {s : State} {B : Addr} {Z w N n c p a : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p) (ha : wordsVal s.mem B (arr w aA) (nu n + 1) = a)
    (hap : a < p) (hpA : p < 2 ^ (64 * nu n)) :
    WP isa double s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aA, aT3, aT1] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w aA) (nu n + 1) = (2 * a) % p ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have n1 : aT1 < N := by unfold aT1; omega
  rw [double]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (one11_ok s) fun t1 ⟨⟨r5, m1⟩, k1⟩ => ?_
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
    (by rw [keep_wv K2 (by omega) (by decide) (by simp) (fit _ nM), hp]) v2') fun t3 ⟨h3, K3, v3, k3⟩ => ?_
  refine ⟨h3, (K2.mono (by simp)).trans (K3.mono (by simp)), ?_, ((k1.mono (by decide)).trans' k2).trans' k3⟩
  rw [v3]
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- After `k` doublings. -/
def DoubleAt (s₀ : State) (B : Addr) (Z w N n p a₀ : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n (5 * (3 * nu n + 2) - k) ∧
    wordsVal t.mem B (arr w aA) (nu n + 1) = Rsa.Divstep.doubled p a₀ k ∧
    KeyWorkspace.Keep B w [aA, aT3, aT1] [] s₀.mem t.mem ∧ Keep (.r10 :: kRegs) s₀ t

theorem shl4 {k : Nat} (h : 16 * k < 2 ^ 64) : BitVec.ofNat 64 k <<< 4 = BitVec.ofNat 64 (16 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `doublings`: `[a] = a 2^(5 (3 ν + 2)) mod p`. -/
theorem doublings_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n 0) (hN : N ≤ 256)
    (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p) (ha : wordsVal s.mem B (arr w aA) (nu n + 1) = a)
    (hap : a < p) (hpA : p < 2 ^ (64 * nu n)) :
    WP isa doublings s (DoubleAt s B Z w N n p a (5 * (3 * nu n + 2))) := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nM : aMz < N := by unfold aMz; omega
  rw [doublings, WP.seq_iff]
  refine WP.mono (WP.keep [.r3, .r8, .r10] (Q := fun u =>
    u.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * (5 * (3 * nu n + 2))) ∧ u.mem = s.mem) ?_ (by decide))
    fun t0 ⟨⟨r10, m0⟩, k0⟩ => ?_
  · have e := h.r10
    simp only [Nat.mul_zero, Nat.add_zero] at e
    have := h.nlt
    have c0 : (BitVec.ofNat 64 n <<< 49) >>> 49 = BitVec.ofNat 64 n := by simpa using cnt_eq (c := 0) h.nlt
    prun [cntN, e, c0, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega),
      shl4 (show 16 * nu n < 2 ^ 64 by omega)]
    have : nu n = (n + 1) / 2 := rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have h0 : Ctx t0 B Z w N n (5 * (3 * nu n + 2)) :=
    ⟨h.ws.of_keep k0, r10, h.npos, h.nw, h.room, by omega, h.wbig, h.fit⟩
  refine count_loop (by omega) (DoubleAt s B Z w N n p a) (fun k hk t ⟨Ht, vt, Kt, kt⟩ => ?_)
    ⟨by simpa using h0, by rw [m0, ha, Rsa.Divstep.doubled_zero hap],
      by rw [m0]; exact KeyWorkspace.Keep.refl _ _ _ _ _, k0.mono (by decide)⟩
  have pt : wordsVal t.mem B (arr w aMz) (nu n + 1) = p := by
    rw [keep_wv Kt (by omega) (by decide) (by simp) (fit _ nM), hp]
  rw [WP.seq_iff]
  refine WP.mono (double_ok Ht hN pt vt (Rsa.Divstep.doubled_lt (by omega)) hpA) fun u ⟨Hu, Ku, vu, ku⟩ => ?_
  rw [show 5 * (3 * nu n + 2) - k = (5 * (3 * nu n + 2) - k - 1) + 1 by omega] at Hu
  refine WP.mono (countDown_ok Hu) fun y ⟨⟨Hy, ry, ym⟩, ky⟩ => ?_
  rw [show 5 * (3 * nu n + 2) - k - 1 = 5 * (3 * nu n + 2) - (k + 1) by omega] at Hy
  exact ⟨⟨Hy, by rw [ym, vu, Rsa.Divstep.doubled_next], Kt.trans (by rw [ym]; exact Ku),
    kt.trans' ((ku.mono (by decide)).trans' (ky.mono (by decide)))⟩, by rw [ry]; omega⟩

/-! ## The end -/

/-- `zeroW j`: `[j]`'s `w + 2` digits zeroed. -/
theorem zeroW_ok {s : State} {B : Addr} {Z w N n c j : Nat} (h : Ctx s B Z w N n c) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (4 * (w + 2)) s.mem t.mem ∧ (∀ i < w + 2, w32 t.mem B (arr w j + 4 * i) = 0) ∧
      Keep kRegs s t :=
  WP.mono (zeroW_ws_ok h.ws hj hN) fun _ ⟨_, K, o, z, k⟩ => ⟨h.of_keep (k.mono (by decide)), K, o, z, k.mono (by decide)⟩

/-- `K` digits holding `v < 2^(32 W)`, the digits from `K` to `W` zero: the `W`
digits are `v`. -/
theorem num_of_val {m : Mem} {B : Addr} {d K W v : Nat} (hv : val32 m B d K = v) (hvW : v < 2 ^ (32 * W))
    (hz : ∀ i, K ≤ i → i < W → w32 m B (d + 4 * i) = 0) : val32 m B d W = v := by
  by_cases hKW : K ≤ W
  · have e1 := val32_append m B d K (W - K)
    have z : val32 m B (d + 4 * K) (W - K) = 0 := val32_zero (fun i hi => by
      rw [show d + 4 * K + 4 * i = d + 4 * (K + i) by omega]; exact hz _ (by omega) (by omega))
    rw [show K + (W - K) = W by omega, hv, z, Nat.mul_zero, Nat.add_zero] at e1
    exact e1
  · have e := val32_append m B d W (K - W)
    rw [show W + (K - W) = K by omega, hv] at e
    have := val32_lt m B d W
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * W) (K - W)) with z | z
    · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
    · have : 2 ^ (32 * W) ≤ 2 ^ (32 * W) * val32 m B (d + 4 * W) (K - W) := Nat.le_mul_of_pos_right _ z
      omega

/-- `ν + 1` words of zero digits. -/
theorem words_of_zero {m : Mem} {B : Addr} {d k W : Nat} (hk : 2 * k ≤ W) (hz : ∀ i < W, w32 m B (d + 4 * i) = 0) :
    wordsVal m B d k = 0 := by
  rw [wordsVal_eq_val32]; exact val32_zero fun i hi => hz i (by omega)

/-- `finishG`: `[1] = |f|`, `w` digits. -/
theorem finishG_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256) {f : Int}
    (hf : (wordsVal s.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = f % 2 ^ (64 * (nu n + 1)))
    (hfr : f.natAbs < 2 ^ (64 * nu n)) :
    WP isa finishG s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aGcd, aT1] [] s.mem t.mem ∧
      num t.mem B w aGcd = f.natAbs ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nG : aGcd < N := by unfold aGcd; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have fG := fit _ nG
  have habs : ((f.natAbs : Nat) : Int) = if f < 0 then -f else f := by
    split
    · exact Int.ofNat_natAbs_of_nonpos (by omega)
    · exact Int.natAbs_of_nonneg (by omega)
  have hfr' : ((f.natAbs : Nat) : Int) < 2 ^ (64 * nu n) := by exact_mod_cast hfr
  obtain ⟨vF, sF⟩ := sign_word hf (by split at habs <;> omega) (by split at habs <;> omega)
  have hQI : ((2 ^ (64 * (nu n + 1)) : Nat) : Int) = 2 ^ (64 * (nu n + 1)) := by push_cast; rfl
  rw [finishG]; simp only [seqs]; rw [WP.seq_iff]
  -- `[1] = 0`.
  refine WP.mono (zeroW_ok h nG hN) fun t1 ⟨h1, K1, out1, z1, k1⟩ => ?_
  rw [WP.seq_iff]
  -- `[aT1] = -f`.
  refine WP.mono (subW_ok h1 n1 nG nF hN) fun t3 ⟨h3, K3, v3, k3⟩ => ?_
  have zG : wordsVal t1.mem B (arr w aGcd) (nu n + 1) = 0 := words_of_zero (W := w + 2) (by omega) z1
  rw [zG, keep_wv K1 hk1 (by decide) (by simp) (fit _ nF)] at v3
  refine WP.mono (signSel_ok h3 nF nG nF n1 hN (by decide)) fun t4 ⟨h4, K4, v4, out4, k4⟩ => ?_
  have K13 : KeyWorkspace.Keep B w [aGcd, aT1] [] s.mem t3.mem := (K1.mono (by simp)).trans (K3.mono (by simp))
  have wF : word t3.mem B (arr w aF + 8 * nu n) = word s.mem B (arr w aF + 8 * nu n) :=
    keep_word K13 (o := 8 * nu n) (b := 64) (by omega) (by decide) (by simp) (fit _ nF)
  rw [wF, keep_wv K13 hk1 (by decide) (by simp) (fit _ nF)] at v4
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
      cases hc : t3.ca <;> simp only [hc, Bool.toNat_false, Bool.toNat_true] at v3 <;> omega
    · rw [ite_eq_right (fun h => hneg (sF.mp h))]
      rw [ite_eq_right hneg] at vF habs
      omega
  have k : Keep kRegs s t4 := (k1.trans' k3).trans' k4
  refine ⟨h4, K13.trans (K4.mono (by simp)), ?_, k⟩
  have hnw : 2 ^ (64 * nu n) ≤ 2 ^ (32 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  refine num_of_val (K := 2 * (nu n + 1)) (by rw [← wordsVal_eq_val32]; exact gcd1) (by omega) fun i hi1 hi2 => ?_
  have e4 : w32 t4.mem B (arr w aGcd + 4 * i) = w32 t3.mem B (arr w aGcd + 4 * i) := by
    unfold w32; rw [Outside.readW32 out4 (by omega) (by omega)]
  have e3 : w32 t3.mem B (arr w aGcd + 4 * i) = w32 t1.mem B (arr w aGcd + 4 * i) := by
    unfold w32; rw [keep_word K3 (o := 4 * i) (b := 32) (by omega) (by decide) (by simp) (fit _ nG)]
  rw [e4, e3]; exact z1 i (by omega)

/-- `finishY`: `[3] = y`, `w` digits. -/
theorem finishY_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256) {y : Nat}
    (hy : wordsVal s.mem B (arr w aA) (nu n + 1) = y) (hyr : y < 2 ^ (32 * w)) :
    WP isa finishY s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aY] [] s.mem t.mem ∧
      num t.mem B w aY = y ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nY : aY < N := by unfold aY; omega
  have nA : aA < N := by unfold aA; omega
  have fY := fitZ _ nY
  have fA := fitZ _ nA
  have fY' := fit _ nY
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  rw [finishY]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (zeroW_ok h nY hN) fun t5 ⟨h5, K5, out5, z5, k5⟩ => ?_
  have hb6 : WP isa (.block (ptr .r5 aY ++ ptr .r6 aA ++ cntN1)) t5 fun u => Ctx u B Z w N n c ∧ u.mem = t5.mem ∧
      u.gpr .r5 = off B (arr w aY) ∧ u.gpr .r6 = off B (arr w aA) ∧ u.gpr .r8 = BitVec.ofNat 64 (nu n + 1) ∧
      Keep kRegs t5 u := by
    rw [List.append_assoc]
    refine ptr_ok h5.ws (by decide) (by decide) (by decide) (by decide) ?_
    refine ptr_ok (h5.ws.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide) (by decide) ?_
    have kt : Keep [.r5, .r6] t5 ((t5.write .r5 (off B (arr w aY))).write .r6 (off B (arr w aA))) :=
      ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono (by decide)
    refine WP.mono (cntN1_ok (h5.of_keep (kt.mono (by decide)))) fun x ⟨⟨x8, xm⟩, kx⟩ => ?_
    have k0 : Keep kRegs t5 x := (kt.trans kx).mono (by decide)
    refine ⟨h5.of_keep k0, by rw [xm]; rfl, ?_, ?_, x8, k0⟩
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, ↓reduceIte]
  rw [WP.seq_iff]
  refine WP.mono hb6 fun t6 ⟨h6, m6, q5, q6, q8, k6⟩ => ?_
  refine WP.mono (copyWLoop_ok h6.ws.scr q5 q6 q8 (by omega) (by omega) (by omega) (by omega)
    (aheadW_k (by decide) (by omega))) fun t7 ⟨v7, out7, k7, _⟩ => ?_
  rw [m6] at v7 out7
  have K57 : KeyWorkspace.Keep B w [aY] [] s.mem t7.mem := K5.trans
    (KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out7) (by omega) (by simp))
  have yA : wordsVal t5.mem B (arr w aA) (nu n + 1) = y := by
    rw [keep_wv K5 hk1 (by decide) (by simp) (fit _ nA), hy]
  have k : Keep kRegs s t7 := (k5.trans' k6).trans' (k7.mono (by decide))
  refine ⟨h.of_keep k, K57, ?_, k⟩
  refine num_of_val (K := 2 * (nu n + 1)) (by rw [← wordsVal_eq_val32, v7, yA]) hyr fun i hi1 hi2 => ?_
  have e7 : w32 t7.mem B (arr w aY + 4 * i) = w32 t5.mem B (arr w aY + 4 * i) := by
    unfold w32; rw [Outside.readW32 out7 (by omega) (by omega)]
  rw [e7]; exact z5 i (by omega)

end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE: the start

`init_ok`: from `x` in array 0 and the odd `m` in array 8, both below
`2^(32 n)`, the start of the inversion modulo `m` (`Divstep.invRunS 59`'s
state 0): `f = m`, `g = oddInput m x`, `a = 0`, `b = 1`, `d = 1`, with
`-m⁻¹ mod 2^64` in the window and `3 ν + 2` batches to run.
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (copyWLoop_ok zerosW_ok)
open VG.Proof.Rsa.Divstep (oddInput)

/-- `initA`: `r10 = n`, `[2] = m`, `ν` words and a zero word `ν`. -/
theorem initA_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {m : Nat} (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n)) :
    WP isa initA s fun t => Ctx t B Z w N n 0 ∧ KeyWorkspace.Keep B w [aMz] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w aMz) (nu n) = m ∧ wordsVal t.mem B (arr w aMz) (nu n + 1) = m ∧
      Keep (.r10 :: kRegs) s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have hnw' := h.nowrap
  have hν : 2 * nu n ≤ w := by unfold nu; omega
  have hν1 : 1 ≤ nu n := by unfold nu; omega
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.arr_fit hj
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have nM : aMz < N := by unfold aMz; omega
  have nI : aMin < N := by unfold aMin; omega
  have fM := fitZ _ nM
  have fI := fitZ _ nI
  have hmν : m < 2 ^ (32 * (2 * nu n)) := by
    have := pow_nu n; rw [show 32 * (2 * nu n) = 64 * nu n by omega]; omega
  simp only [initA, seqs]
  -- `r10 = n`, `[2] = m`, `ν` words.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (WP.keep [.r8, .r10] (Q := fun u => u.gpr .r10 = BitVec.ofNat 64 n ∧
    u.gpr .r8 = BitVec.ofNat 64 (nu n) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u10, u8, um⟩, ku⟩ => ?_
  · have c0 : (BitVec.ofNat 64 n <<< 49) >>> 49 = BitVec.ofNat 64 n := by
      simpa using cnt_eq (n := n) (c := 0) (by omega)
    prun [cntN, h11, BitVec.add_zero, c0, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega)]
  have k1 : Keep (.r10 :: kRegs) s u := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans ku).mono (by decide)
  have h1 : Ctx u B Z w N n 0 := ⟨h.of_keep k1, by rw [u10]; simp, hn1, hnw, hN15, by decide, hw, hfit⟩
  refine WP.mono (copyWLoop_ok (dO := arr w aMz) (dA := arr w aMin) h1.ws.scr
    (by rw [ku.gpr _ (by decide)]; simp [gpr_write]) (by rw [ku.gpr _ (by decide)]; simp [gpr_write]) u8 hν1
    (by omega) (by omega) (by omega) (aheadW_k (by decide) (by omega))) fun t1 ⟨v1, out1, kt1, _⟩ => ?_
  rw [um] at v1 out1
  have k1' : Keep (.r10 :: kRegs) s t1 := k1.trans' (kt1.mono (by decide))
  have h1' := h1.of_keep (kt1.mono (by decide))
  have mI : wordsVal s.mem B (arr w aMin) (nu n) = m := by
    rw [wordsVal_eq_val32]; exact num_of_val hm hmν (fun i h1 h2 => absurd h1 (by omega))
  rw [mI] at v1
  -- Its word `ν` zero.
  refine topOf_ok h1' nM hN fun x hx xm x6 kx => ?_
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = x.mem.writeW (off B (arr w aMz + 8 * nu n))
      (0 : BitVec 64)) ?_ (by decide)) fun t2 ⟨m2, k2⟩ => ?_
  · prun [x6, hx.ws.scr.st (show arr w aMz + 8 * nu n + 8 ≤ Z by omega)]
    rfl
  have k : Keep (.r10 :: kRegs) s t2 := (k1'.trans' (kx.mono (by decide))).trans' (k2.mono (by decide))
  rw [xm] at m2
  have o2 := writeW_outside t1.mem B (d := arr w aMz + 8 * nu n) (0 : BitVec 64) (by omega)
  have v2 : wordsVal t2.mem B (arr w aMz) (nu n) = m := by
    rw [m2, o2.wordsVal (by omega) (by omega), v1]
  refine ⟨hx.of_keep (k2.mono (by decide)), ?_, v2, ?_, k⟩
  · exact (KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out1) (by omega) (by simp)).trans
      (by rw [m2]; exact KeyWorkspace.Keep.of_arr (d := 8 * nu n) o2 (by omega) (by simp))
  · rw [m2, Loops.wordsVal_write_top _ _ _ _ _ (by omega), v1]; rfl

/-- A Newton step: `a x' ≡ 1 (mod 2^(2j))` from `a x ≡ 1 (mod 2^j)`, `a` in
`r5` and `x` in `r6`. -/
theorem newton_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .r5).toNat : Int) * (t.gpr .r6).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      ((((t'.gpr .r5).toNat : Int) * (t'.gpr .r6).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
        t'.gpr .r5 = t.gpr .r5 ∧ t'.mem = t.mem) ∧ Keep [.r3, .r4, .r6] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun [newton]
  exact VG.Proof.Bignum.newton_step hj h (Bignum.PPC64LE.Pub.newton_val _ _)

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
theorem initB_ok {t7 : State} {B : Addr} {Z w N n c : Nat} (h7 : Ctx t7 B Z w N n c) {m : Nat}
    (pv : wordsVal t7.mem B (arr w aMz) (nu n + 1) = m) (hodd : m % 2 = 1) :
    WP isa initB t7 fun t9 => Ctx t9 B Z w N n c ∧ KeyWorkspace.Keep B w [aW] [] t7.mem t9.mem ∧
      (∃ iv, (m * iv + 1) % 2 ^ 64 = 0 ∧ (t9.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) ∧
      Keep kRegs t7 t9 := by
  have h := h7
  have hS : S w = 4 * (w + 2) := rfl
  have := h.ws.wle
  have := h.wbig
  have room := h.room
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nW : aW < N := by unfold aW; omega
  have fM := fitZ _ nM
  have fW := fitZ _ nW
  have hnw := h.ws.nowrap
  have d0p : (word t7.mem B (arr w aMz)).toNat % 2 ^ 64 = m % 2 ^ 64 := by
    have e : wordsVal t7.mem B (arr w aMz) (nu n + 1) =
        (word t7.mem B (arr w aMz)).toNat + 2 ^ 64 * wordsVal t7.mem B (arr w aMz + 8) (nu n) := rfl
    rw [pv] at e; omega
  have hd := (word t7.mem B (arr w aMz)).isLt
  rw [initB, show ptr .r4 aMz ++ ([.load .d .r5 .r4 0, .addi .r6 .r5 0] : List Instr) ++ newton ++ newton ++
      newton ++ newton ++ newton ++ ([.li .r3 0, .sub .r12 .r3 .r6] : List Instr) ++ ptr .r4 aW ++
      ([.store .d .r12 .r4 wIv] : List Instr) =
    (ptr .r4 aMz ++ ([.load .d .r5 .r4 0, .addi .r6 .r5 0] : List Instr)) ++ (newton ++ (newton ++ (newton ++
      (newton ++ (newton ++ (([.li .r3 0, .sub .r12 .r3 .r6] : List Instr) ++ ptr .r4 aW ++
        ([.store .d .r12 .r4 wIv] : List Instr))))))) by
    simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r4, .r5, .r6] (Q := fun u => u.gpr .r5 = word t7.mem B (arr w aMz) ∧
      u.gpr .r6 = word t7.mem B (arr w aMz) ∧ u.mem = t7.mem) ?_ (by decide))
    fun u0 ⟨⟨u5, u6, um⟩, k0⟩ => ?_
  · prun [ptr, word, exec_load_d, exec_li (imm := aMz) (by decide),
      exec_addi (n := .r4) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h.ptr aMz,
      BitVec.add_zero, h.ws.scr.ld (show arr w aMz + 8 ≤ Z by omega)]
  have e₀ : (((u0.gpr .r5).toNat : Int) * (u0.gpr .r6).toNat - 1) % (2 ^ 3 : Int) = 0 := by
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
  refine WP.mono (WP.keep [.r3, .r4, .r12] (Q := fun u => u.mem = u5'.mem.writeW (off B (arr w aW + 40))
      (BitVec.ofNat 64 0 - u5'.gpr .r6)) ?_ (by decide)) fun t9 ⟨m9, k9⟩ => ?_
  · prun [ptr, wIv, exec_store_d, exec_li (imm := aW) (by decide),
      exec_addi (n := .r4) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h5.ptr aW,
      off_add, h5.ws.scr.st (show arr w aW + 40 + 8 ≤ Z by omega)]
  have h9 := h5.of_keep (k9.mono (by decide))
  have o9 := writeW_outside u5'.mem B (d := arr w aW + 40) (BitVec.ofNat 64 0 - u5'.gpr .r6) (by omega)
  have b5 : u5'.gpr .r5 = word t7.mem B (arr w aMz) := by rw [b₅, b₄, b₃, b₂, b₁, u5]
  rw [b5] at e₅
  have F9 : KeyWorkspace.Keep B w [aW] [] t7.mem t9.mem := by
    rw [m9, ← m05]; exact KeyWorkspace.Keep.of_arr (o := aW) (d := 40) o9 (by omega) (by simp)
  refine ⟨h9, F9, ⟨(BitVec.ofNat 64 0 - u5'.gpr .r6).toNat, ?_, by
    rw [m9, show arr w aW + wIv = arr w aW + 40 from rfl, Mem.readW_writeW_self64]⟩,
    Keep.trans' k05 (k9.mono (by decide))⟩
  have nv := neg_inv64 e₅
  have e2 : (BitVec.ofNat 64 0 - u5'.gpr .r6).toNat = (2 ^ 64 - (u5'.gpr .r6).toNat % 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e2, Nat.add_mod, Nat.mul_mod, ← d0p, Nat.mod_mod]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] at nv
  exact nv

end VG.Proof.Rsa.PPC64LE.InvBatch

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (copyWLoop_ok zerosW_ok)
open VG.Proof.Rsa.Divstep (oddInput)

/-- Bit 0 of a word, inverted. -/
theorem even_bit64 (x : BitVec 64) :
    ((x &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1).toNat = (if x.toNat % 2 = 0 then 1 else 0) := by
  rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e <;> rw [e] <;> rfl

/-- `[j] = 0`, `ν + 1` words. -/
theorem zeroN_ok {s : State} {B : Addr} {Z w N n c j : Nat} (h : Ctx s B Z w N n c) (hj : j < N) (hN : N ≤ 256) :
    WP isa (.seq (.block (ptr .r5 j ++ cntN1 ++ ([.li .r0 0] : List Instr))) zerosW) s fun t =>
      Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧ wordsVal t.mem B (arr w j) (nu n + 1) = 0 ∧
      Keep kRegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  have fj := h.ws.arr_fit hj
  rw [WP.seq_iff, List.append_assoc]
  refine ptr_ok h.ws (by decide) (by decide) (by decide) (by omega) ?_
  rw [WP.block_append_iff]
  refine WP.mono (cntN1_ok (h.of_keep ((Keep.write _ .r5 _).mono (by decide)))) fun x ⟨⟨q8, xm⟩, kx⟩ => ?_
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.gpr .r0 = 0 ∧ u.mem = x.mem) (by prun; rfl) (by decide))
    fun y ⟨⟨y0, ym⟩, ky⟩ => ?_
  have ka : Keep kRegs s y := (((Keep.write _ .r5 _).trans kx).trans ky).mono (by decide)
  refine WP.mono (zerosW_ok (dO := arr w j) (m := nu n + 1) (h.of_keep ka).ws.scr
    (by rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; simp [gpr_write])
    (by rw [ky.gpr _ (by decide)]; exact q8) y0 (by omega) (by omega) (by omega))
    fun t ⟨z, out, kt⟩ => ?_
  rw [ym, xm, mem_write] at out
  exact ⟨h.of_keep (ka.trans' (kt.mono (by decide))),
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega) (by simp), z,
    ka.trans' (kt.mono (by decide))⟩

/-- `initC`: `f = m`, `g = oddInput m x`, `(a, b) = (0, 1)`, `d = 1` and `3 ν + 2` batches. -/
theorem initC_ok {t9 : State} {B : Addr} {Z w N n : Nat} (h9 : Ctx t9 B Z w N n 0) (hN : N ≤ 256)
    {x m iv : Nat} (hx : wordsVal t9.mem B (arr w aX) (nu n) = x)
    (pv9 : wordsVal t9.mem B (arr w aMz) (nu n + 1) = m) (pv9' : wordsVal t9.mem B (arr w aMz) (nu n) = m)
    (hivw : (t9.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) :
    WP isa initC t9 fun t => Ctx t B Z w N n (3 * nu n + 2) ∧
      BS t B w n m iv (Divstep.invRunS 59 m iv (oddInput m x) 0) ∧
      KeyWorkspace.Keep B w [aW, aF, aG, aA, aB] [] t9.mem t.mem ∧ Keep (.r10 :: kRegs) t9 t := by
  have hS : S w = 4 * (w + 2) := rfl
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
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  simp only [initC, seqs]
  -- `f = m`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc]
  refine ptr_ok h9.ws (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h9.ws.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide) (by decide) ?_
  have kt : Keep [.r5, .r6] t9 ((t9.write .r5 (off B (arr w aF))).write .r6 (off B (arr w aMz))) :=
    ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono (by decide)
  refine WP.mono (cntN1_ok (h9.of_keep (kt.mono (by decide)))) fun x10 ⟨⟨q8, xm⟩, kx⟩ => ?_
  have k10a : Keep kRegs t9 x10 := (kt.trans kx).mono (by decide)
  have h10a := h9.of_keep k10a
  refine WP.mono (copyWLoop_ok (dO := arr w aF) (dA := arr w aMz) h10a.ws.scr
    (by rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte])
    (by rw [kx.gpr _ (by decide)]; simp only [gpr_write, ↓reduceIte]) q8
    (by omega) (by omega) (by omega) (by omega) (aheadW_k (by decide) (by omega)))
    fun t10 ⟨vF, out10, k10, _⟩ => ?_
  have xm' : x10.mem = t9.mem := xm
  rw [xm', pv9] at vF
  rw [xm'] at out10
  have h10 := h10a.of_keep (k10.mono (by decide))
  have a10 : KeyWorkspace.Keep B w [aF] [] t9.mem t10.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by omega) (by simp)
  -- `k = 1` for an even `x`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r5, .r11] (Q := fun u => (u.gpr .r11).toNat =
      (if (word t10.mem B (arr w aX)).toNat % 2 = 0 then 1 else 0) ∧ u.mem = t10.mem) ?_ (by decide))
    fun t11 ⟨⟨r11k, m11⟩, k11⟩ => ?_
  · prun [ptr, word, exec_load_d, exec_li (imm := aX) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h10.ptr aX,
      BitVec.add_zero, h10.ws.scr.ld (show arr w aX + 8 ≤ Z by omega)]
    exact even_bit64 _
  have h11' := h10.of_keep (k11.mono (by decide))
  have xX : wordsVal t11.mem B (arr w aX) (nu n) = x := by
    rw [m11, keep_wv a10 hk0 (by decide) (by simp) (fit _ nX), hx]
  have x0 : (word t10.mem B (arr w aX)).toNat % 2 = x % 2 := by
    rw [← m11, ← xX]
    obtain ⟨k, hk⟩ : ∃ k, nu n = k + 1 := ⟨nu n - 1, by omega⟩
    rw [hk]; simp only [wordsVal]; omega
  have pM : wordsVal t11.mem B (arr w aMz) (nu n) = m := by
    rw [m11, keep_wv a10 hk0 (by decide) (by simp) (fit _ nM), pv9']
  -- `g = x + k m`, its carry the word `ν`.
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h11' (fun u hu => cntN_ok hu) (K := nu n) (by omega) (by omega) nG nX nM hN)
    fun t12 ⟨h12, K12, v12, p12, _, _, out12, k12⟩ => ?_
  rw [xX, pM, r11k, x0] at v12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t12.mem.writeW (off B (arr w aG + 8 * nu n))
      (t12.gpr .r9)) ?_ (by decide)) fun t13 ⟨m13, k13⟩ => ?_
  · prun [p12, exec_store_d, h12.ws.scr.st (show arr w aG + 8 * nu n + 8 ≤ Z by omega)]
  have h13 := h12.of_keep (k13.mono (by decide))
  have vG : wordsVal t13.mem B (arr w aG) (nu n + 1) = oddInput m x := by
    rw [m13, Loops.wordsVal_write_top _ _ _ _ _ (by omega)]
    unfold oddInput
    by_cases e : x % 2 = 0 <;> simp only [e, ↓reduceIte] at v12 ⊢ <;> omega
  have a13 : KeyWorkspace.Keep B w [aG] [] t12.mem t13.mem := by
    rw [m13]; exact KeyWorkspace.Keep.of_arr (d := 8 * nu n) (writeW_outside _ B _ (by omega)) (by omega) (by simp)
  -- `a = 0`, `b = 0`.
  rw [WP.seq_iff]
  refine WP.mono (zeroN_ok h13 nA hN) fun t14 ⟨h14, a14, z14, k14⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (zeroN_ok h14 nB hN) fun t15 ⟨h15, a15, z15, k15⟩ => ?_
  -- `b = 1`, `d = 1` and `3 ν + 2` batches.
  refine WP.mono (WP.keep [.r0, .r3, .r5, .r8, .r10] (Q := fun u => u.mem = (t15.mem.writeW (off B (arr w aB))
      (BitVec.ofNat 64 1)).writeW (off B (arr w aW)) (BitVec.ofNat 64 1) ∧
      u.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * (3 * nu n + 2))) ?_ (by decide))
    fun t16 ⟨⟨m16, r16⟩, k16⟩ => ?_
  · have e := h15.r10
    simp only [Nat.mul_zero, Nat.add_zero] at e
    have := h15.nlt
    have c0 : (BitVec.ofNat 64 n <<< 49) >>> 49 = BitVec.ofNat 64 n := by simpa using cnt_eq (c := 0) h15.nlt
    prun [ptr, wD, exec_store_d, exec_li (imm := aB) (by decide), exec_li (imm := aW) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h15.ptr aB, h15.ptr aW,
      BitVec.add_zero, cntN, e, c0, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega),
      h15.ws.scr.st (show arr w aB + 8 ≤ Z by omega), h15.ws.scr.st (show arr w aW + 8 ≤ Z by omega)]
    have : nu n = (n + 1) / 2 := rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  -- The result.
  have oB := writeW_outside t15.mem B (d := arr w aB) (BitVec.ofNat 64 1) (by omega)
  have oW := writeW_outside (t15.mem.writeW (off B (arr w aB)) (BitVec.ofNat 64 1)) B (d := arr w aW)
    (BitVec.ofNat 64 1) (by omega)
  have F16 : KeyWorkspace.Keep B w [aB, aW] [] t15.mem t16.mem := by
    rw [m16]
    exact (KeyWorkspace.Keep.of_arr (o := aB) (d := 0) (by simpa only [Nat.add_zero] using oB) (by omega)
      (by simp)).trans
      (KeyWorkspace.Keep.of_arr (o := aW) (d := 0) (by simpa only [Nat.add_zero] using oW) (by omega) (by simp))
  have K11 : KeyWorkspace.Keep B w [] [] t10.mem t11.mem := by rw [m11]; exact KeyWorkspace.Keep.refl _ _ _ _ _
  have KF : KeyWorkspace.Keep B w [aG, aA, aB, aW] [] t10.mem t16.mem :=
    (K11.mono (by simp)).trans ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans ((a14.mono (by simp)).trans
      ((a15.mono (by simp)).trans (F16.mono (by simp))))))
  have KG : KeyWorkspace.Keep B w [aA, aB, aW] [] t13.mem t16.mem :=
    (a14.mono (by simp)).trans ((a15.mono (by simp)).trans (F16.mono (by simp)))
  have KA : KeyWorkspace.Keep B w [aB, aW] [] t14.mem t16.mem := (a15.mono (by simp)).trans (F16.mono (by simp))
  have Kall : KeyWorkspace.Keep B w [aW, aF, aG, aA, aB] [] t9.mem t16.mem :=
    (a10.mono (by simp)).trans (KF.mono (by simp))
  have KnoW : KeyWorkspace.Keep B w [aF, aG, aA, aB] [] t9.mem t15.mem :=
    (a10.mono (by simp)).trans ((K11.mono (by simp)).trans ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans
      ((a14.mono (by simp)).trans (a15.mono (by simp))))))
  have k : Keep (.r10 :: kRegs) t9 t16 :=
    (((((k10a.trans' (k10.mono (by decide))).trans' (k11.mono (by decide))).trans' (k12.trans' (k13.mono
      (by decide)))).trans' (k14.trans' k15)).mono (by decide)).trans' (k16.mono (by decide))
  have e0 : Divstep.invRunS 59 m iv (oddInput m x) 0 = ⟨1, m, oddInput m x, 0, 1⟩ := rfl
  rw [e0]
  refine ⟨⟨h15.ws.of_keep k16, r16, h.npos, h.nw, h.room, by omega, h.wbig, h.fit⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, Kall, k⟩
  · show t16.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 1
    rw [show arr w aW + wD = arr w aW from rfl, m16, Mem.readW_writeW_self64]; rfl
  · show (wordsVal t16.mem B (arr w aF) (nu n + 1) : Int) % _ = (m : Int) % _
    rw [keep_wv KF hk1 (by decide) (by simp) (fit _ nF), vF]
  · show (wordsVal t16.mem B (arr w aG) (nu n + 1) : Int) % _ = (oddInput m x : Int) % _
    rw [keep_wv KG hk1 (by decide) (by simp) (fit _ nG), vG]
  · show (wordsVal t16.mem B (arr w aA) (nu n + 1) : Int) % _ = (0 : Int) % _
    rw [keep_wv KA hk1 (by decide) (by simp) (fit _ nA), z14]; rfl
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
      Mem.readW_congr fun i hi => oB _ (by
        rw [ofs_off B (by omega)]; have := arr_disj (w := w) (show aB ≠ aW by decide); omega),
      keep_word KnoW w40 (by decide) (by simp) (fit _ nW)]
    exact hivw
  · rw [keep_wv Kall hk0 (by decide) (by simp) (fit _ nM), pv9']
  · rw [keep_wv Kall hk1 (by decide) (by simp) (fit _ nM), pv9]

/-- `init`: the start of the inversion modulo `m`. -/
theorem init_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {x m : Nat} (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n))
    (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa init s fun t => Ctx t B Z w N n (3 * nu n + 2) ∧
      (∃ iv, (m * iv + 1) % 2 ^ 64 = 0 ∧ BS t B w n m iv (Divstep.invRunS 59 m iv (oddInput m x) 0)) ∧
      KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA, aB] [] s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hS : S w = 4 * (w + 2) := rfl
  have hν : 2 * nu n ≤ w := by unfold nu; omega
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have hk0 : 8 * nu n ≤ S w := by omega
  have nX : aX < N := by unfold aX; omega
  have nM : aMz < N := by unfold aMz; omega
  rw [init]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (initA_ok h hN15 hN hw h11 hn1 hnw hfit hm hmn) fun t7 ⟨h7, K7, pv', pv, k7⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (initB_ok h7 pv hodd) fun t9 ⟨h9, K9, ⟨iv, hiv, hivw⟩, k9⟩ => ?_
  have K79 : KeyWorkspace.Keep B w [aMz, aW] [] s.mem t9.mem := (K7.mono (by simp)).trans (K9.mono (by simp))
  have hxν : x < 2 ^ (32 * (2 * nu n)) := by
    have := pow_nu n; rw [show 32 * (2 * nu n) = 64 * nu n by omega]; omega
  have hx' : wordsVal s.mem B (arr w aX) (nu n) = x := by
    rw [wordsVal_eq_val32]; exact num_of_val hx hxν (fun i h1 h2 => absurd h1 (by omega))
  refine WP.mono (initC_ok h9 hN (x := x) (m := m)
    (by rw [keep_wv K79 hk0 (by decide) (by simp) (fit _ nX), hx'])
    (by rw [keep_wv K9 hk1 (by decide) (by simp) (fit _ nM), pv])
    (by rw [keep_wv K9 hk0 (by decide) (by simp) (fit _ nM), pv']) hivw) fun t ⟨ht, st, K, kt⟩ => ?_
  exact ⟨ht, ⟨iv, hiv, st⟩, (K79.mono (by simp)).trans (K.mono (by simp)),
    (k7.trans' (k9.mono (by decide))).trans' kt⟩

end VG.Proof.Rsa.PPC64LE.InvBatch

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Proof.Rsa.Divstep (oddInput)

/-- The run's result after `3 ν + 2` batches: `|f| = gcd(m, x)` and the congruence. -/
theorem run_done [Divstep.TcSLaw] {n m iv x : Nat} (hodd : m % 2 = 1) (hiv : (m * iv + 1) % 2 ^ 64 = 0)
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
  obtain ⟨-, hfI, hcong⟩ := Divstep.TcSLaw.invRunS_done (N := 59) (B := 3 * nu n + 2) (by decide) hodd hmI hdone
  refine ⟨hfI, ?_⟩
  rw [show 5 * (3 * nu n + 2) = (64 - 59) * (3 * nu n + 2) by omega]
  exact hcong

/-- The inputs below `2^(32 n)`, from the contract, as the inverse's bounds. -/
theorem inputs_lt {n m x : Nat} (hmn : m < 2 ^ (32 * n)) (hxn : x < 2 ^ (32 * n)) :
    m < 2 ^ (64 * nu n) ∧ oddInput m x < 2 * 2 ^ (64 * nu n) := by
  have := pow_nu n
  have ox : oddInput m x ≤ m + x := by unfold oddInput; split <;> omega
  omega

/-- The arrays `inverse` writes. -/
abbrev invArrs : List Nat := [1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14]

/-- The registers `inverse` changes. -/
abbrev invRegs : List Reg := .r10 :: kRegs

/-- The congruence of `y` scaled by `2^(5 (3 ν + 2))`. -/
theorem scaled_cong {m x : Nat} {y : Nat} {I : Divstep.IState} {k : Nat}
    (c2 : (y : Int) ≡ (if 0 ≤ I.f then 1 else -1) * I.a [ZMOD m])
    (hcong : (x : Int) * ((if 0 ≤ I.f then 1 else -1) * I.a) * 2 ^ k ≡ (Nat.gcd m x : Int) [ZMOD m]) :
    ((y * 2 ^ k % m : Nat) : Int) * x ≡ (Nat.gcd m x : Int) [ZMOD m] := by
  refine Int.ModEq.trans ?_ hcong
  push_cast
  have h1 : ((y : Int) * 2 ^ k) % m * x ≡ (y : Int) * 2 ^ k * x [ZMOD m] := (Int.mod_modEq _ _).mul_right _
  refine h1.trans ?_
  have h2 := (c2.mul_right ((2 : Int) ^ k)).mul_right (x : Int)
  refine h2.trans ?_
  rw [show (if 0 ≤ I.f then 1 else -1) * I.a * 2 ^ k * (x : Int) =
    (x : Int) * ((if 0 ≤ I.f then 1 else -1) * I.a) * 2 ^ k by ring]

theorem inverse_ok [Divstep.TcSLaw] {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {x m : Nat} (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m)
    (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa inverse s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have := h.wle
  have hν : 2 * nu n ≤ w := by unfold nu; omega
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hS : S w = 4 * (w + 2) := rfl
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nM : aMz < N := by unfold aMz; omega
  have nG : aGcd < N := by unfold aGcd; omega
  obtain ⟨pc, xc⟩ := inputs_lt hmn hxn
  have hw32 : 2 ^ (32 * n) ≤ 2 ^ (32 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [inverse, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN15 hN hw h11 hn1 hnw hfit hx hxn hm hmn hodd)
    fun t0 ⟨h0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 st0 hodd (by omega) hiv pc xc) fun t1 ⟨h1, st1, K1, k1⟩ => ?_
  rw [Nat.sub_self] at h1
  obtain ⟨-, -, -, -, ha, -⟩ := run_bounds (k := 3 * nu n + 2) hodd hiv pc xc
  obtain ⟨hfI, hcong⟩ := run_done hodd hiv hmn hxn (by omega)
  generalize Divstep.invRunS 59 m iv (oddInput m x) (3 * nu n + 2) = I at st1 ha hfI hcong
  have gle : Nat.gcd m x ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hf1 : -(m : Int) ≤ I.f := by omega
  have hf2 : I.f ≤ m := by omega
  rw [WP.seq_iff]
  refine WP.mono (normalize_ok h1 hN st1.P1 pc st1.a ha.1 ha.2 st1.f hf1 hf2) fun t2 ⟨h2, K2, y2, c2, k2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (doublings_ok h2 hN (by rw [keep_wv K2 hk1 (by decide) (by simp) (fit _ nM)]; exact st1.P1) rfl y2 pc)
    fun t3 ⟨h3, v3, K3, k3⟩ => ?_
  rw [Nat.sub_self] at h3
  have hf3 : (wordsVal t3.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1)) := by
    rw [keep_wv K3 hk1 (by decide) (by simp) (fit _ nF), keep_wv K2 hk1 (by decide) (by simp) (fit _ nF)]; exact st1.f
  have hyr := Rsa.Divstep.doubled_lt (p := m) (a := wordsVal t2.mem B (arr w aA) (nu n + 1))
    (k := 5 * (3 * nu n + 2)) (by omega)
  rw [finish, WP.seq_iff]
  refine WP.mono (finishG_ok h3 hN hf3 (by rw [hfI]; omega)) fun t4 ⟨h4, K4, g4, k4⟩ => ?_
  refine WP.mono (finishY_ok h4 hN (y := Rsa.Divstep.doubled m (wordsVal t2.mem B (arr w aA) (nu n + 1))
    (5 * (3 * nu n + 2))) (by rw [keep_wv K4 hk1 (by decide) (by simp) (fit _ nA)]; exact v3) (by omega))
    fun t5 ⟨h5, K5, y5, k5⟩ => ?_
  refine ⟨h5.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K3.mono (by decide)).trans ((K4.mono (by decide)).trans (K5.mono (by decide))))))),
    ((((k0.trans' k1).trans' (k2.mono (by decide))).trans' k3).trans' (k4.mono (by decide))).trans'
      (k5.mono (by decide)), fun _ => ?_⟩
  have g5 : num t5.mem B w 1 = I.f.natAbs := by
    rw [show (1 : Nat) = aGcd from rfl, ← g4]; exact keep_val K5 (by omega) (by decide) (by simp) (fit _ nG)
  rw [show aY = 3 from rfl] at y5
  rw [g5, y5, hfI]
  exact ⟨Nat.gcd_comm _ _, (scaled_cong c2 hcong).symm.dvd, hyr⟩

theorem inverseS_ok [Divstep.TcSLaw] {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {x m : Nat} (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m)
    (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa inverseS s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ ((num t.mem B w 3 * 2 ^ (5 * (3 * ((n + 1) / 2) + 2)) % m : Nat) : Int) * x -
          num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have := h.wle
  have hν : 2 * nu n ≤ w := by unfold nu; omega
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hS : S w = 4 * (w + 2) := rfl
  have hk1 : 8 * (nu n + 1) ≤ S w := by omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nG : aGcd < N := by unfold aGcd; omega
  obtain ⟨pc, xc⟩ := inputs_lt hmn hxn
  have hw32 : 2 ^ (32 * n) ≤ 2 ^ (32 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [inverseS, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN15 hN hw h11 hn1 hnw hfit hx hxn hm hmn hodd)
    fun t0 ⟨h0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 st0 hodd (by omega) hiv pc xc) fun t1 ⟨h1, st1, K1, k1⟩ => ?_
  obtain ⟨-, -, -, -, ha, -⟩ := run_bounds (k := 3 * nu n + 2) hodd hiv pc xc
  obtain ⟨hfI, hcong⟩ := run_done hodd hiv hmn hxn (by omega)
  generalize Divstep.invRunS 59 m iv (oddInput m x) (3 * nu n + 2) = I at st1 ha hfI hcong
  have gle : Nat.gcd m x ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hf1 : -(m : Int) ≤ I.f := by omega
  have hf2 : I.f ≤ m := by omega
  rw [WP.seq_iff]
  refine WP.mono (normalize_ok h1 hN st1.P1 pc st1.a ha.1 ha.2 st1.f hf1 hf2) fun t2 ⟨h2, K2, y2, c2, k2⟩ => ?_
  have hf3 : (wordsVal t2.mem B (arr w aF) (nu n + 1) : Int) % 2 ^ (64 * (nu n + 1)) = I.f % 2 ^ (64 * (nu n + 1)) := by
    rw [keep_wv K2 hk1 (by decide) (by simp) (fit _ nF)]; exact st1.f
  rw [finish, WP.seq_iff]
  refine WP.mono (finishG_ok h2 hN hf3 (by rw [hfI]; omega)) fun t4 ⟨h4, K4, g4, k4⟩ => ?_
  refine WP.mono (finishY_ok h4 hN (y := wordsVal t2.mem B (arr w aA) (nu n + 1))
    (by rw [keep_wv K4 hk1 (by decide) (by simp) (fit _ nA)]) (by omega)) fun t5 ⟨h5, K5, y5, k5⟩ => ?_
  refine ⟨h5.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K4.mono (by decide)).trans (K5.mono (by decide)))))),
    (((k0.trans' k1).trans' (k2.mono (by decide))).trans' (k4.mono (by decide))).trans' (k5.mono (by decide)),
    fun _ => ?_⟩
  have g5 : num t5.mem B w 1 = I.f.natAbs := by
    rw [show (1 : Nat) = aGcd from rfl, ← g4]; exact keep_val K5 (by omega) (by decide) (by simp) (fit _ nG)
  rw [show aY = 3 from rfl] at y5
  rw [g5, y5, hfI]
  exact ⟨Nat.gcd_comm _ _, (scaled_cong c2 hcong).symm.dvd, y2⟩

/-- `gcd(x, m)` alone, by the batches of `f` and `g`. -/
theorem gcd_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {x m : Nat} (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m)
    (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa gcd s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m) := by
  have := h.wle
  have hν : 2 * nu n ≤ w := by unfold nu; omega
  obtain ⟨pc, xc⟩ := inputs_lt hmn hxn
  simp only [gcd, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN15 hN hw h11 hn1 hnw hfit hx hxn hm hmn hodd)
    fun t0 ⟨h0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loopG_ok hN h0 st0.toBG hodd hiv pc xc) fun t1 ⟨h1, st1, K1, k1⟩ => ?_
  obtain ⟨hfI, -⟩ := run_done hodd hiv hmn hxn (by omega)
  have gle : Nat.gcd m x ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  refine WP.mono (finishG_ok h1 hN st1.f (by rw [hfI]; omega)) fun t2 ⟨h2, K2, g2, k2⟩ => ?_
  refine ⟨h2.ws, (K0.mono (by decide)).trans ((K1.mono (by decide)).trans (K2.mono (by decide))),
    (k0.trans' k1).trans' (k2.mono (by decide)), fun _ => ?_⟩
  rw [show (1 : Nat) = aGcd from rfl, g2, hfI, Nat.gcd_comm]

end VG.Proof.Rsa.PPC64LE.InvBatch

namespace VG.Proof.Rsa.PPC64LE

instance invLaw [Divstep.TcSLaw] : InvLaw where
  inverse_ok := InvBatch.inverse_ok
  inverseS_ok := InvBatch.inverseS_ok
  gcd_ok := InvBatch.gcd_ok

end VG.Proof.Rsa.PPC64LE
