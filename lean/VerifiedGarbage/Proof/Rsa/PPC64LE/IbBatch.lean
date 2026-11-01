module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbRed
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.Batch
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

end VG.Proof.Rsa.PPC64LE.InvBatch
