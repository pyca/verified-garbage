import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombStagesCT

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
variable {c : Impl.Ecdsa.X86.Cfg}

/-- Inputs to the fixed-base multiplication, after converting `u` to bits. -/
structure VCombInput (c : Impl.Ecdsa.X86.Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends
    Keep c s₀ base s where
  scalar : ∃ k, k < 2 ^ (64 * c.n) ∧
    (∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0

theorem vBits_ok (hc : CfgOk c) {s₀ s : State} {base : Addr} (h : Mid c s₀ base s) :
    WP isa (Impl.Weierstrass.X86.bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) s
      (VCombInput c s₀ base) := by
  have h7 := hc.n10
  refine WP.mono (bits_ok h.scr hc.n0 (sl_le c h7 (i := U) (by decide)) (tbl_le h7)
    (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega))) fun t ⟨b, k, o⟩ => ?_
  have unch : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem t.mem := o.unch
  have v : ∀ {i}, i < 45 → sv c base t i = sv c base s i := fun hi =>
    sv_unch unch h7 h.scr.nowrap hi (apart_tbl hi 0)
  have hsc : (⟨base, size⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk] :=
    List.mem_append_left _ (by rw [← h.wr]; exact h.scr.wr)
  exact ⟨⟨h.scr.of_keeps k (by decide), (k.gpr _ (by decide)).trans h.esp,
    k.rd.trans h.rd, k.wr.trans h.wr, h.fixed.unch h7 h.scr.nowrap (fixedOk_tbl 0) unch,
    h.whole.trans (frame_of_unch unch (fun w hw => by rw [List.mem_singleton.mp hw]; exact tbl_le h7) hsc),
    h.sp_lo⟩,
    ⟨sv c base s U, wordsVal_lt _ _ _ _, b⟩,
    (v (by decide)).trans h.rx, (v (by decide)).trans h.ry, (v (by decide)).trans h.rz⟩

/-- Read-only comb tables outside the working space. -/
def VCombTables (s : State) : Prop :=
  TblMem s ((s.gpr .eax).setWidth 64) (p256Comb.combWords p256d) ∧
  (∀ i < (p256Comb.combWords p256d).length, ∀ b < 8,
    size ≤ ofs (ptr s 3) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) ∧
  ∀ r ∈ s.wr ++ [below (s.gpr .esp) p256Comb.stk],
    Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 8 * (p256Comb.combWords p256d).length⟩ r

theorem vTables_keep {s₀ s : State} (ht : VCombTables s₀) (K : Keep p256Comb s₀ (ptr s₀ 3) s) :
    TblMem s ((s₀.gpr .eax).setWidth 64) (p256Comb.combWords p256d) ∧
      ∀ r ∈ s.wr ++ [below (s.gpr .esp) 20],
        Region.Disjoint ⟨(s₀.gpr .eax).setWidth 64, 8 * (p256Comb.combWords p256d).length⟩ r :=
  K.tbls ht.1 ht.2.2

theorem vPoints_keep (hc : CfgOk p256Comb) (hC : Law p256Comb.C) (hT : CombTbls p256Comb)
    (hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d) (ham3 : AM3 p256Comb.C)
    {s₀ s : State} (ht : VCombTables s₀) (h : Mid p256Comb s₀ (ptr s₀ 3) s)
    (hspG : SpOk p256Comb.gMul 20) (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.pointsComb p256Comb) p256Comb.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.pointsComb p256Comb) s (Keep p256Comb s₀ (ptr s₀ 3)) := by
  let P := Ecdh.X86.peerPt p256Comb (s₀.mem (ptr s₀ 0) = 4)
    (keyX p256Comb s₀) (keyY p256Comb s₀)
  have hPc : onCurve p256Comb.C P = true := Ecdh.X86.peerPt_onCurve hc _ _ _
  have hQ : Rep p256Comb.C (tmv p256Comb.C p256Comb.n (ptr s₀ 3) s (p256Comb.sl Impl.Ecdh.X86.PX))
      (tmv p256Comb.C p256Comb.n (ptr s₀ 3) s (p256Comb.sl Impl.Ecdh.X86.PY))
      (tmv p256Comb.C p256Comb.n (ptr s₀ 3) s (p256Comb.sl ONEP)) P := by
    obtain ⟨_, _, h1⟩ := consts_tmv hc h.fixed
    rw [h1]
    exact Ecdh.X86.peerPt_rep hC _ _ _ h.px h.py
  have H := pointsComb_ok hc hC hT hCo ham3 h
    (fun d hd => by
      have e : p256d = d := Option.some.inj hd
      subst d
      exact ⟨(vTables_keep ht h.keep).1, ht.2.1, ht.2.2⟩)
    hPc hQ hspG hsp
    (rest := .block []) (fun _ P => WP.block_nil P.keep)
  exact WP.mono (WP.seq_iff.mp H) (fun _ q => WP.block_nil_iff.mp q)

end VG.Proof.Ecdsa.Verify.X86
