module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WideLoop
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNafWide
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
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
