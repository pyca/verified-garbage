module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbRed
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The batched inverse on PPC64LE: a batch

`batch_ok`: from the arrays and the window holding a state of
`Proof/Divstep/Alg32Def.lean`'s inversion (`StateAt`), a batch leaves the next
one: 30 divsteps on the low digits (`head_ok`), then the new `f`, `g`, `a`,
`b` (`update_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)
open VG.Proof.Divstep (MSt msteps WSt)

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

/-- The state of the inversion in the arrays and the window. -/
structure StateAt (s : State) (B : Addr) (w n p iv : Nat) (st : Divstep.W32.IState) : Prop where
  f : sv s.mem B (arr w aF) n = st.f
  g : sv s.mem B (arr w aG) n = st.g
  a : (val32 s.mem B (arr w aA) (n + 1) : Int) = st.a
  b : (val32 s.mem B (arr w aB) (n + 1) : Int) = st.b
  d : s.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 st.d
  iv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv
  p : val32 s.mem B (arr w aMz) (n + 1) = p

/-! ## The divsteps -/

/-- The words the batch's divsteps leave. -/
abbrev mat (st : Divstep.W32.IState) : MSt := msteps 30 (MSt.init st.d st.f st.g)


/-- A signed number is its low digit modulo `2^32`. -/
theorem sv_mod (m : Mem) (B : Addr) (d n : Nat) (hn : 1 ≤ n) :
    sv m B d n % 2 ^ 32 = (w32 m B d : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e : val32 m B d (k + 1) = w32 m B d + 2 ^ 32 * val32 m B (d + 4) k := rfl
  unfold sv
  rw [e, show 32 * (k + 1) = 32 + 32 * k by omega, Int.pow_add]
  have hw := (m.readW (off B d) 32).isLt
  push_cast
  rw [Int.mul_assoc 4294967296]
  generalize (2 : Int) ^ (32 * k) * (m.readW (off B (d + 4 * (k + 1))) 32).toInt = Q
  simp only [w32] at hw ⊢
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

/-- `start`, 30 divsteps and `save`: `d` and the matrix of 30 divsteps from
`(d, f, g)` in the window. -/
theorem head_ok {s : State} {B : Addr} {Z w N n c p iv : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n c) (hst : StateAt s B w n p iv st) (hN : N ≤ 256)
    (hd : |st.d| + 60 < 2 ^ 62) (hf : st.f % 2 = 1) :
    WP isa (.block (start ++ wsteps 30 ++ save)) s fun t => Ctx t B Z w N n c ∧
      KeyWorkspace.Keep B w [aW] [] s.mem t.mem ∧ Outside B (arr w aW) 40 s.mem t.mem ∧
      t.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 (mat st).d ∧
      t.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat st).u ∧
      t.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat st).v ∧
      t.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat st).q ∧
      t.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat st).r ∧ Keep kRegs s t := by
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
  -- The start: the low digits, `d` and the identity.
  have hs1 : WP isa (.block start) s fun t => (regsW t = ⟨BitVec.ofInt 64 st.d,
      (s.mem.readW (off B (arr w aF)) 32).setWidth 64, (s.mem.readW (off B (arr w aG)) 32).setWidth 64,
      BitVec.ofNat 64 1, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 1⟩ ∧ t.mem = s.mem) ∧
      Keep kRegs s t := by
    have hd0 : s.mem.readW (off B (arr w aW)) 64 = BitVec.ofInt 64 st.d := by
      simpa only [wD, Nat.add_zero] using hst.d
    refine WP.keep _ ?_ (by decide)
    prun [start, ldW, ptr, regsW, wD, exec_li (imm := aF) (by decide), exec_li (imm := aG) (by decide),
      exec_li (imm := aW) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      exec_addi (n := .r3) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      hdr_eq, h.ptr aF, h.ptr aG, h.ptr aW, h.ws.scr.ld (show arr w aF + 4 ≤ Z by omega),
      h.ws.scr.ld (show arr w aG + 4 ≤ Z by omega), h.ws.scr.ld (show arr w aW + 8 ≤ Z by omega), hd0]
  refine WP.mono hs1 fun t1 ⟨⟨r1, m1⟩, k1⟩ => ?_
  refine WP.mono (wsteps_ok 30 t1) fun t2 ⟨⟨r2, m2⟩, k2⟩ => ?_
  have h2 := h.of_keep (k1.trans' k2)
  -- The words of the divsteps.
  have rel : (regsW t1).rel (MSt.init st.d st.f st.g) 30 := by
    rw [r1]
    have e := sv_mod s.mem B (arr w aF) n h.npos
    have e' := sv_mod s.mem B (arr w aG) n h.npos
    rw [hst.f] at e
    rw [hst.g] at e'
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show ((((s.mem.readW (off B (arr w aF)) 32).setWidth 64).toNat : Nat) : Int) % 2 ^ 30 = st.f % 2 ^ 30
      rw [toNat_ext32, show (2 : Int) ^ 30 = 2 ^ 30 from rfl, ← Int.emod_emod_of_dvd st.f (show (2 : Int) ^ 30 ∣ 2 ^ 32 by decide), e]
    · show ((((s.mem.readW (off B (arr w aG)) 32).setWidth 64).toNat : Nat) : Int) % 2 ^ 30 = st.g % 2 ^ 30
      rw [toNat_ext32, ← Int.emod_emod_of_dvd st.g (show (2 : Int) ^ 30 ∣ 2 ^ 32 by decide), e']
  have R := Divstep.wsteps_rel (by decide) rel (by simpa [MSt.init] using hd) hf 30 (Nat.le_refl _)
  rw [← r2] at R
  obtain ⟨Rd, Ru, Rv, Rq, Rr, -, -⟩ := R
  refine WP.mono (save_ok h2) fun t3 ⟨m3, k3⟩ => ?_
  have hW : aW < N := by have := h.room; unfold aW; omega
  have fW := h.ws.arr_fit hW
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

/-! ## The update -/

theorem natAbs_bnd {u v : Int} (h : |u| + |v| ≤ 2 ^ 30) : u.natAbs + v.natAbs ≤ 2 ^ 30 := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h; omega

/-- A number below `2^(32 n)` in `n + 1` digits, as a signed number. -/
theorem sv_of_val {m : Mem} {B : Addr} {d n : Nat} {a : Int} (h : (val32 m B d (n + 1) : Int) = a)
    (h1 : a < 2 ^ (32 * n)) : sv m B d n = a :=
  sv_of_eq (q := 0) (by rw [h, Int.mul_zero, Int.add_zero]) (by
    have : (0 : Int) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.zero_le _
    omega) (by
    have : (2 : Int) ^ (32 * n) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
    omega)

/-- `update`: the new `f`, `g`, `a` and `b` from the matrix in the window. -/
theorem update_ok {s : State} {B : Addr} {Z w N n c p iv cap : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hf : sv s.mem B (arr w aF) n = st.f) (hg : sv s.mem B (arr w aG) n = st.g)
    (ha : (val32 s.mem B (arr w aA) (n + 1) : Int) = st.a) (hb : (val32 s.mem B (arr w aB) (n + 1) : Int) = st.b)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv)
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat st).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat st).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat st).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat st).r)
    (hodd : st.f % 2 = 1) (hfc : |st.f| ≤ cap) (hgc : |st.g| ≤ cap) (hcap : cap < 2 ^ (32 * n + 1))
    (ha0 : 0 ≤ st.a) (ha1 : st.a < p) (hb0 : 0 ≤ st.b) (hb1 : st.b < p) (hpA : p < 2 ^ (32 * n)) (hp0 : 0 < p)
    (hinv : (p * iv + 1) % 2 ^ 32 = 0) :
    WP isa update s fun t => Ctx t B Z w N n c ∧
      KeyWorkspace.Keep B w [aF, aG, aA, aB, aT1, aT2, aT3] [] s.mem t.mem ∧
      sv t.mem B (arr w aF) n = (Divstep.W32.batch 30 p iv st).f ∧
      sv t.mem B (arr w aG) n = (Divstep.W32.batch 30 p iv st).g ∧
      (val32 t.mem B (arr w aA) (n + 1) : Int) = (Divstep.W32.batch 30 p iv st).a ∧
      (val32 t.mem B (arr w aB) (n + 1) : Int) = (Divstep.W32.batch 30 p iv st).b ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have hnw := h.ws.nowrap
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd st.d st.f st.g 30
  obtain ⟨ef, eg⟩ := Divstep.msteps_mat (d := st.d) (g := st.g) hodd 30
  change 2 ^ 30 * (mat st).f = (mat st).u * st.f + (mat st).v * st.g at ef
  change 2 ^ 30 * (mat st).g = (mat st).q * st.f + (mat st).r * st.g at eg
  change |(mat st).u| + |(mat st).v| ≤ 2 ^ 30 at bu
  change |(mat st).q| + |(mat st).r| ≤ 2 ^ 30 at bq
  -- The new values.
  have nf : (Divstep.W32.batch 30 p iv st).f = (mat st).f := by
    show ((mat st).u * st.f + (mat st).v * st.g) / 2 ^ 30 = (mat st).f
    rw [← ef, Int.mul_ediv_cancel_left _ (by decide)]
  have ng : (Divstep.W32.batch 30 p iv st).g = (mat st).g := by
    show ((mat st).q * st.f + (mat st).r * st.g) / 2 ^ 30 = (mat st).g
    rw [← eg, Int.mul_ediv_cancel_left _ (by decide)]
  have nfc : |(mat st).f| ≤ cap := by
    have := Divstep.W32.comb_le bu hfc hgc
    rw [← ef, abs_mul, abs_of_pos (by decide : (0 : Int) < 2 ^ 30)] at this
    exact le_of_mul_le_mul_left this (by decide)
  have ngc : |(mat st).g| ≤ cap := by
    have := Divstep.W32.comb_le bq hfc hgc
    rw [← eg, abs_mul, abs_of_pos (by decide : (0 : Int) < 2 ^ 30)] at this
    exact le_of_mul_le_mul_left this (by decide)
  have rng : ∀ z : Int, |z| ≤ cap → -2 ^ (32 * n + 31) ≤ z ∧ z < 2 ^ (32 * n + 31) := by
    intro z hz
    rw [abs_le] at hz
    have : (2 : Int) ^ (32 * n + 1) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
    have : (cap : Int) < 2 ^ (32 * n + 1) := by exact_mod_cast hcap
    omega
  have hpI : (p : Int) < 2 ^ (32 * n) := by exact_mod_cast hpA
  have sa := sv_of_val ha (by omega)
  have sb := sv_of_val hb (by omega)
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nW : aW < N := by unfold aW; omega
  have w8 : ∀ o, o + 8 ≤ 48 → o + 64 / 8 ≤ S w := fun o ho => by have := h.wbig; omega
  have hk : n + 1 ≤ w + 2 := by omega
  have hk2 : n + 1 + 1 ≤ w + 2 := by omega
  simp only [update, seqs]
  -- 1, 2: `u f + v g` and `q f + r g`.
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h n1 nF nG hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hU hV (natAbs_bnd bu)) fun t1 ⟨h1, K1, e1, k1⟩ => ?_
  rw [hf, hg, ← ef] at e1
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h1 n2 nF nG hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hQ)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hR) (natAbs_bnd bq))
    fun t2 ⟨h2, K2, e2, k2⟩ => ?_
  rw [keep_sv K1 (by omega) (by decide) (by simp) (fit _ nF), keep_sv K1 (by omega) (by decide) (by simp)
    (fit _ nG), hf, hg, ← eg] at e2
  -- 3, 4: the new `f` and `g`.
  rw [WP.seq_iff]
  refine WP.mono (shr_ok h2 nF n1 hN (by decide) (z := (mat st).f)
    (by rw [keep_sv K2 hk2 (by decide) (by simp) (fit _ n1)]; exact e1) (rng _ nfc).1 (rng _ nfc).2)
    fun t3 ⟨h3, K3, e3, k3⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (shr_ok h3 nG n2 hN (by decide) (z := (mat st).g)
    (by rw [keep_sv K3 hk2 (by decide) (by simp) (fit _ n2)]; exact e2) (rng _ ngc).1 (rng _ ngc).2)
    fun t4 ⟨h4, K4, e4, k4⟩ => ?_
  -- What the arrays `a`, `b` and the window hold still.
  have K14 : KeyWorkspace.Keep B w [aT1, aT2, aF, aG] [] s.mem t4.mem :=
    (K1.mono (by simp)).trans ((K2.mono (by simp)).trans ((K3.mono (by simp)).trans (K4.mono (by simp))))
  have wd : ∀ o, o + 8 ≤ 48 → t4.mem.readW (off B (arr w aW + o)) 64 = s.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => keep_word K14 (w8 _ ho) (by decide) (by simp) (fit _ nW)
  -- 5, 6: `u a + v b` and `q a + r b`.
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h4 n1 nA nB hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [wd _ (by decide)]; exact hU) (by rw [wd _ (by decide)]; exact hV) (natAbs_bnd bu))
    fun t5 ⟨h5, K5, e5, k5⟩ => ?_
  rw [keep_sv K14 (by omega) (by decide) (by simp) (fit _ nA), keep_sv K14 (by omega) (by decide) (by simp)
    (fit _ nB), sa, sb] at e5
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h5 n2 nA nB hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_word K5 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW), wd _ (by decide)]; exact hQ)
    (by rw [keep_word K5 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW), wd _ (by decide)]; exact hR)
    (natAbs_bnd bq)) fun t6 ⟨h6, K6, e6, k6⟩ => ?_
  rw [keep_sv K5 (by omega) (by decide) (by simp) (fit _ nA), keep_sv K5 (by omega) (by decide) (by simp)
    (fit _ nB), keep_sv K14 (by omega) (by decide) (by simp) (fit _ nA), keep_sv K14 (by omega) (by decide)
    (by simp) (fit _ nB), sa, sb] at e6
  have K16 : KeyWorkspace.Keep B w [aT1, aT2, aF, aG] [] s.mem t6.mem :=
    K14.trans ((K5.mono (by simp)).trans (K6.mono (by simp)))
  have small : ∀ x y : Int, |x| + |y| ≤ 2 ^ 30 → |x * st.a + y * st.b| ≤ 2 ^ 31 * (p : Int) := by
    intro x y hxy
    have := Divstep.W32.comb_le hxy (p := p) (by rw [abs_of_nonneg ha0]; omega) (by rw [abs_of_nonneg hb0]; omega)
    have : (0 : Int) ≤ p := by omega
    calc |x * st.a + y * st.b| ≤ 2 ^ 30 * (p : Int) := by assumption
      _ ≤ 2 ^ 31 * (p : Int) := Int.mul_le_mul_of_nonneg_right (by decide) this
  -- 7, 8: the new `a` and `b`.
  rw [WP.seq_iff]
  refine WP.mono (mred_ok h6 n1 nA hN n3 nM (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_val K16 hk (by decide) (by simp) (fit _ nM)]; exact hp) hpA hp0
    (by rw [keep_word K16 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hiv) hinv
    (by rw [keep_sv K6 hk2 (by decide) (by simp) (fit _ n1)]; exact e5) (small _ _ bu))
    fun t7 ⟨h7, K7, e7, k7⟩ => ?_
  refine WP.mono (mred_ok h7 n2 nB hN n3 nM (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_val K7 hk (by decide) (by simp) (fit _ nM), keep_val K16 hk (by decide) (by simp) (fit _ nM), hp])
    hpA hp0
    (by rw [keep_word K7 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW), keep_word K16 (w8 _ (by decide))
      (by decide) (by simp) (fit _ nW), hiv]) hinv
    (by rw [keep_sv K7 hk2 (by decide) (by simp) (fit _ n2)]; exact e6) (small _ _ bq))
    fun t8 ⟨h8, K8, e8, k8⟩ => ?_
  have k : Keep kRegs s t8 := ((((((k1.trans' k2).trans' k3).trans' k4).trans' k5).trans' k6).trans' k7).trans' k8
  have K58 : KeyWorkspace.Keep B w [aT1, aT2, aA, aB, aT3] [] t4.mem t8.mem :=
    (K5.mono (by simp)).trans ((K6.mono (by simp)).trans ((K7.mono (by simp)).trans (K8.mono (by simp))))
  refine ⟨h.of_keep k, (K14.mono (by simp)).trans (K58.mono (by simp)), ?_, ?_, ?_, ?_, k⟩
  · rw [keep_sv K58 (by omega) (by decide) (by simp) (fit _ nF), keep_sv K4 (by omega) (by decide) (by simp)
      (fit _ nF), e3, nf]
  · rw [keep_sv K58 (by omega) (by decide) (by simp) (fit _ nG), e4, ng]
  · rw [keep_val K8 hk (by decide) (by simp) (fit _ nA), e7, Divstep.W32.batch_a]
  · rw [e8, Divstep.W32.batch_b]

end VG.Proof.Rsa.PPC64LE.InvBatch
