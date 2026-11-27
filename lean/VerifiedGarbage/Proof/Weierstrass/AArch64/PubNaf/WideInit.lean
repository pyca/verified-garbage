module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Prep
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Weierstrass.AArch64.PubNaf.WideLoop`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNafWide
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Impl.Weierstrass.AArch64.PubNafWide
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 PubNaf
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
theorem byte_word (k j : Nat) :
 BitVec.ofNat 8 (BitVec.ofInt 64 (FastNaf7.digit k j)).toNat=FastNaf7.byte k j := fastByte_word 7 k j

structure PrepSt (n : Nat) (base : Addr) (size bits k j : Nat) (s : State) : Prop where
  scr : Scr s base size
  value : regsVal s (limbs n) = FastNaf7.residual k j
  mask : s.gpr (cst n 0) = 127
  sign : s.gpr (cst n 1) = 64
  zero : s.gpr (cst n 2) = 0
  one : s.gpr (cst n 3) = 1
  count : s.gpr .x19 = BitVec.ofNat 64 (64 * n + 1 - j)
  ptr : s.gpr .x20 = off base (bits + j)
  digits : ∀ i < j, s.mem (off base (bits + i)) = FastNaf7.byte k i

theorem digitStore_ok {s : State} {base : Addr} {size bits k j : Nat}
    (hs : Scr s base size) (hbj : bits + j < size)
    (hp : s.gpr .x20 = off base (bits + j))
    (hd : s.gpr .x2 = BitVec.ofInt 64 (FastNaf7.digit k j)) :
    WP isa (.block ([.strb .x2 .x20 0, .addImm .x .x20 .x20 1] : List Instr)) s fun t =>
      t.gpr .x20 = off base (bits + (j + 1)) ∧
      t.mem = s.mem.writeW (off base (bits + j)) (FastNaf7.byte k j) ∧ KeepRegs [.x20] s t := by
  rw [show ([.strb .x2 .x20 0, .addImm .x .x20 .x20 1] : List Instr) =
    [.strb .x2 .x20 0] ++ [.addImm .x .x20 .x20 1] from rfl, WP.block_append_iff]
  have hw : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 0) 1 := by
    rw [hp]; simp only [BitVec.add_zero]
    exact ⟨_, hs.wr, hs.contains (by omega_arith) (by decide)⟩
  refine WP.mono (strb_ok s (by decide) hw) fun a ha => ?_
  subst a
  refine WP.mono (addImm_ok _ (d := .x20) (n := .x20) (imm := 1) (by decide)) fun t ⟨ht, kt⟩ => ?_
  refine ⟨?_, ?_, ⟨kt.gpr, kt.rd, kt.wr, kt.sp⟩⟩
  · rw [ht]; change s.gpr .x20 + BitVec.ofNat 64 1 = _
    rw [hp]; unfold off; rw [Offset.add_add]; congr 1
  · rw [kt.mem]; simp only [hp, BitVec.add_zero, hd, byte_word]

theorem prepStep_ok {n : Nat} (hR : Regs n) {s : State} {base : Addr} {size bits k j : Nat}
    (hI : PrepSt n base size bits k j s) (hb : bits + (64 * n + 1) ≤ size) (hj : j < 64 * n + 1)
    (hv : FastNaf7.residual k j ≤ 2 ^ (64 * n)) :
    WP isa (prepStep n) s fun t => PrepSt n base size bits k (j + 1) t ∧
      KeepRegs (clobs n) s t ∧ Outside base bits (64 * n + 1) s.mem t.mem := by
  have cn : ∀ {i}, i < 4 → cst n i ∉ [Reg.x1, .x2, .x3] ∧ cst n i ∉ [Reg.x20] ∧
      cst n i ∉ Reg.x3 :: limbs n ∧ cst n i ∉ [Reg.x19] := fun hi => by
    obtain ⟨a1, a2, a3, a19, a20⟩ := hR.cst_ne hi
    have := hR.cst_notin hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨a1, a2, a3⟩, a20, ⟨a3, this⟩, a19⟩
  have ln : ∀ r ∈ limbs n, r ∉ [Reg.x1, .x2, .x3] ∧ r ∉ [Reg.x20] := fun r hr => by
    have := hR.limb_ne hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨⟨this.2.1, this.2.2.1, this.2.2.2.1⟩, this.2.2.2.2.2.2.2.2⟩
  rw [prepStep]
  refine WP.seq (WP.mono (chooseDigit_ok hR s hI.mask hI.sign hI.one) fun a ⟨ha, ka⟩ => ?_)
  have va : regsVal a (limbs n) = FastNaf7.residual k j :=
    (regsVal_congr fun r hr => ka.gpr r (ln r hr).1).trans hI.value
  have da : a.gpr .x2 = BitVec.ofInt 64 (FastNaf7.digit k j) := by
    rw [ha]; apply fastRaw7_eq
    have hh := hI.value
    rw [limbs_eq hR, regsVal] at hh
    omega_arith
  have pa : a.gpr .x20 = off base (bits + j) := (ka.gpr _ (by decide)).trans hI.ptr
  have sa := hI.scr.of_keeps ka (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (digitStore_ok sa (by omega_arith) pa da) fun b ⟨pb, mb, kb⟩ => ?_
  have sb := sa.of_keepRegs kb (by decide)
  have vb : regsVal b (limbs n) = FastNaf7.residual k j :=
    (regsVal_congr fun r hr => kb.gpr r (ln r hr).2).trans va
  rw [WP.block_append_iff]
  refine WP.mono (subtractShift_ok hR b k j
    (by rw [kb.gpr _ (cn (by decide)).2.1, ka.gpr _ (cn (by decide)).1, hI.zero])
    (by rw [kb.gpr .x2 (by decide)]; exact da) vb hv) fun c ⟨vc, kc⟩ => ?_
  have pc : c.gpr .x20 = off base (bits + (j + 1)) := (kc.gpr _ (by
    intro h; exact (hR.limb_ne (r := .x20) (by simpa using h)) (by simp))).trans pb
  have sc := sb.of_keeps kc (by
    intro h; exact (hR.limb_ne (r := .x0) (by simpa using h)) (by simp))
  have cc : c.gpr .x19 = BitVec.ofNat 64 (64 * n + 1 - j) := by
    rw [kc.gpr _ (by intro h; exact (hR.limb_ne (r := .x19) (by simpa using h)) (by simp)),
      kb.gpr _ (by decide), ka.gpr _ (by decide), hI.count]
  have hle := hR.le
  refine WP.mono (decCounter_ok c (by omega_arith) (by omega_arith) cc) fun t ⟨ct, kt⟩ => ?_
  have st := sc.of_keeps kt (by decide)
  have mt : t.mem = s.mem.writeW (off base (bits + j)) (FastNaf7.byte k j) := by
    rw [kt.mem, kc.mem, mb, ka.mem]
  have O := writeW8_outside s.mem base (FastNaf7.byte k j) (d := bits + j) (by have := hI.scr.nowrap; omega_arith)
  have keepC : ∀ {i}, i < 4 → t.gpr (cst n i) = s.gpr (cst n i) := fun hi => by
    rw [kt.gpr _ (cn hi).2.2.2, kc.gpr _ (cn hi).2.2.1, kb.gpr _ (cn hi).2.1, ka.gpr _ (cn hi).1]
  refine ⟨⟨st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [regsVal_congr fun r hr => kt.gpr r (by
      intro h; exact (hR.limb_ne hr) (by simp only [List.mem_singleton] at h; simp [h]))]
    exact vc
  · rw [keepC (by decide), hI.mask]
  · rw [keepC (by decide), hI.sign]
  · rw [keepC (by decide), hI.zero]
  · rw [keepC (by decide), hI.one]
  · rw [ct]; congr 1
  · rw [kt.gpr _ (by decide), pc]
  · intro i hi
    rw [mt]
    by_cases hij : i = j
    · subst i; exact writeW8_self ..
    · rw [O _ (by
        have hoff : ofs base (off base (bits + i)) = bits + i := ofs_off0 base (by have := hI.scr.nowrap; omega_arith)
        rw [hoff]; omega_arith)]
      exact hI.digits i (by omega_arith)
  · refine ⟨fun r hr => ?_, kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
      kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)), kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
    simp only [clobs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simpa using hr.1.1.2.2.2.1), kc.gpr r (by
        simp only [List.mem_cons, not_or]; exact ⟨hr.1.1.2.2.1, hr.1.2⟩),
      kb.gpr r (by simpa using hr.1.1.2.2.2.2), ka.gpr r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hr.1.1.1, hr.1.1.2.1, hr.1.1.2.2.1⟩)]
  · rw [mt]; exact O.mono (by omega_arith) (by omega_arith)


end VG.Proof.Weierstrass.AArch64.PubNafWide

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.PubNafWide
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Impl.Weierstrass.AArch64.PubNafWide
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 PubNaf
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
theorem init_ok (K : WinCfg) (hR : Regs K.M.n) {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src + 8 * K.M.n ≤ size) (hsrc8 : src % 8 = 0)
    (hbits : K.bits < 4096) :
    WP isa (.block (prepInit7 K src)) s fun t =>
      PrepSt K.M.n base size K.bits (wordsVal s.mem base src K.M.n) 0 t ∧
      KeepRegs (clobs K.M.n) s t ∧ t.mem = s.mem := by
  have hlow : (low K.M.n).Nodup := by
    have := (List.nodup_append.mp hR.nodup).1
    rw [limbs] at this
    exact (List.nodup_append.mp this).1
  have hlx0 : Reg.x0 ∉ low K.M.n := fun h =>
    hR.limb_ne (r := .x0) (List.mem_append_left _ h) (by simp)
  rw [prepInit7, WP.block_append_iff, loads_eq]
  refine WP.mono (loadsR_ok (low K.M.n) hs.ptr (a := src) (by rw [hR.len]; omega_arith) hsrc8 hlow hlx0)
    fun a ⟨va, ka, _⟩ => ?_
  have sa := hs.of_keeps ka hlx0
  -- The distinct registers written.
  have h7 : K.M.n < 10 := by have := hR.le; omega_arith
  obtain ⟨t0, t1, t2, t3, t19, t20⟩ := init_facts1 K.M.n h7
  obtain ⟨c01, c02, c03, c12, c13, c23⟩ := init_facts1' K.M.n h7
  have hlo := init_facts2 K.M.n h7
  have cx := init_facts3 K.M.n h7
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok a (top K.M.n) 0) fun b ⟨db, kb⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok b (cst K.M.n 0) 127) fun c ⟨dc, kc⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok c (cst K.M.n 1) 64) fun d ⟨dd, kd⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok d (cst K.M.n 2) 0) fun e ⟨de, ke⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok e (cst K.M.n 3) 1) fun f ⟨df, kf⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movzW_ok f .x19 _) fun g ⟨dg, kg⟩ => ?_
  refine WP.mono (addImm_ok g (d := .x20) (n := .x0) hbits) fun t ⟨dt, kt⟩ => ?_
  have ks : ∀ r, r ≠ top K.M.n → r ≠ cst K.M.n 0 → r ≠ cst K.M.n 1 → r ≠ cst K.M.n 2 →
      r ≠ cst K.M.n 3 → r ≠ .x19 → r ≠ .x20 → t.gpr r = a.gpr r := fun r h0 h1 h2 h3 h4 h5 h6 => by
    rw [kt.gpr r (by simpa using h6), kg.gpr r (by simpa using h5), kf.gpr r (by simpa using h4),
      ke.gpr r (by simpa using h3), kd.gpr r (by simpa using h2), kc.gpr r (by simpa using h1),
      kb.gpr r (by simpa using h0)]
  have ka0 : a.gpr .x0 = s.gpr .x0 := ka.gpr _ hlx0
  have hl6 := hR.le
  have ne : ∀ {r q : Reg}, r ≠ q → r ∉ [q] := fun h => by simpa using h
  have tTop : t.gpr (top K.M.n) = 0 := by
    rw [kt.gpr _ (ne t20), kg.gpr _ (ne t19), kf.gpr _ (ne t3), ke.gpr _ (ne t2), kd.gpr _ (ne t1),
      kc.gpr _ (ne t0), db]; rfl
  have tC0 : t.gpr (cst K.M.n 0) = 127 := by
    rw [kt.gpr _ (ne (cx 0 (by decide)).2), kg.gpr _ (ne (cx 0 (by decide)).1), kf.gpr _ (ne c03),
      ke.gpr _ (ne c02), kd.gpr _ (ne c01), dc]; rfl
  have tC1 : t.gpr (cst K.M.n 1) = 64 := by
    rw [kt.gpr _ (ne (cx 1 (by decide)).2), kg.gpr _ (ne (cx 1 (by decide)).1), kf.gpr _ (ne c13),
      ke.gpr _ (ne c12), dd]; rfl
  have tC2 : t.gpr (cst K.M.n 2) = 0 := by
    rw [kt.gpr _ (ne (cx 2 (by decide)).2), kg.gpr _ (ne (cx 2 (by decide)).1), kf.gpr _ (ne c23), de]; rfl
  have tC3 : t.gpr (cst K.M.n 3) = 1 := by
    rw [kt.gpr _ (ne (cx 3 (by decide)).2), kg.gpr _ (ne (cx 3 (by decide)).1), df]; rfl
  have t19 : t.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n + 1) := by
    rw [kt.gpr _ (by decide), dg]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  have g0 : g.gpr .x0 = s.gpr .x0 := by
    obtain ⟨z0, z1, z2, z3, z4⟩ := init_facts4 K.M.n h7
    rw [kg.gpr _ (by decide), kf.gpr _ (ne z4.symm), ke.gpr _ (ne z3.symm), kd.gpr _ (ne z2.symm),
      kc.gpr _ (ne z1.symm), kb.gpr _ (ne z0.symm), ka0]
  have hlow' : ∀ r ∈ low K.M.n, t.gpr r = a.gpr r := fun r hr => by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hlo r hr
    exact ks r h0 h1 h2 h3 h4 h5 h6
  have tmem : t.mem = s.mem := by
    rw [kt.mem, kg.mem, kf.mem, ke.mem, kd.mem, kc.mem, kb.mem, ka.mem]
  have twr : t.wr = s.wr := by
    rw [kt.wr, kg.wr, kf.wr, ke.wr, kd.wr, kc.wr, kb.wr, ka.wr]
  refine ⟨⟨⟨?_, twr ▸ hs.wr, hs.nowrap, hs.enc⟩, ?_, tC0, tC1, tC2, tC3, ?_, ?_, fun i hi => absurd hi (by omega_arith)⟩,
    ⟨fun r hr => ?_, ?_, twr, ?_⟩, tmem⟩
  · rw [kt.gpr _ (by decide), g0, hs.x0]
  · rw [limbs, regsVal_append, regsVal_congr hlow', va, hR.len]
    simp only [regsVal, tTop, FastNaf7.residual_zero]
    simp
  · rw [t19]; rfl
  · rw [dt, g0, hs.x0]; simp only [off, Nat.add_zero]
  · simp only [clobs, csts, limbs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨⟨⟨-, -, -, h19, h20⟩, hl, htop⟩, hc0, hc1, hc2, hc3⟩ := hr
    rw [ks r htop hc0 hc1 hc2 hc3 h19 h20]
    exact ka.gpr r hl
  · rw [kt.rd, kg.rd, kf.rd, ke.rd, kd.rd, kc.rd, kb.rd, ka.rd]
  · rw [kt.sp, kg.sp, kf.sp, ke.sp, kd.sp, kc.sp, kb.sp, ka.sp]


end VG.Proof.Weierstrass.AArch64.PubNafWide
