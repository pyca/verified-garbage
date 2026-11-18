module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
meta import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
meta import VerifiedGarbage.Impl.Ecdh.P384.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Impl.P384.EcdhMadd
import VerifiedGarbage.Proof.P384.Ops
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Impl.P384.EcdhMadd
meta import VerifiedGarbage.Proof.P384.Ops
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Impl.P384.EcdhSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Impl.P384.EcdhSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CombEntry
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.P384
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdh.AArch64.P384.Contract`, which only this module used -/

section

/-!
# ECDH over P-384 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdh.P384.exchangeApi`'s contract for AArch64, by name:
`vg_ecdh_p384(out = x0, d = x1, peer = x2, scratch = x3)`, the result in
`w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P384.curve (ofBytes (bytesAt m d 48)) (bytesAt m peer 97)

def ecdhAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 48⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let peer : Region := ⟨s.gpr .x2, 97⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      (s.gpr .x0).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 48 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 97⟩]
  wr := [⟨0x1000, 48⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhAArch64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
        simp only [ecdhAArch64, ex, Spec.P384.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.AArch64.P384

end

end

/-! ### `P384.EcdhSelect`, which only this module used -/

section

/-!
# P-384's entry selection in registers

`sel_ok`: P-384's selection of a digit's entry (`Impl/P384/EcdhSelect.lean`)
does what the window's must (`SelOk`). Candidate `m + 1`'s nine pairs of words
are kept in the accumulators where `|d| = m + 1` (`cand_ok`, by `pair_ok`), so
after the eight candidates the accumulators hold entry `|d|`'s words, or
`(0 : R : 0)`'s for `|d| = 0` (`Acc`), which are stored to `E`.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhSelect
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.P384.EcdhDouble VG.Impl.P384.EcdhSelect
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono pair_ok cmp_ok read_x)

/-- The accumulator of word `q` (`6 c + w`) of the entry. -/
def wReg (q : Nat) : Reg := accReg (q / 6) (q % 6)

theorem wReg_inj : ∀ q < 18, ∀ q' < 18, wReg q = wReg q' → q = q' := by decide

theorem wReg_ne : ∀ q < 18, wReg q ≠ .x0 ∧ wReg q ≠ .x2 ∧ wReg q ≠ .x9 ∧ wReg q ≠ .x16 ∧
    wReg q ≠ .x17 ∧ wReg q ≠ .x19 := by decide

theorem pair_regs : ∀ p < 9, accReg (p / 3) (2 * (p % 3)) = wReg (2 * p) ∧
    accReg (p / 3) (2 * (p % 3) + 1) = wReg (2 * p + 1) := by decide

/-- The accumulators. -/
def wRegs : List Reg := (List.range 18).map wReg

theorem mem_wRegs {q : Nat} (hq : q < 18) : wReg q ∈ wRegs := List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩

/-- Word `q` of `(0 : R : 0)`. -/
def initW (q : Nat) : BitVec 64 := if q / 6 = 1 then wordOf K.one (q % 6) else 0

/-- The accumulators after the candidates `1 … n`: entry `a`'s words at `d`
(`a ≤ n`), else `(0 : R : 0)`'s. -/
def Acc (m0 : Mem) (base : Addr) (d a n : Nat) (s : State) : Prop :=
  ∀ q < 18, s.gpr (wReg q) =
    if 1 ≤ a ∧ a ≤ n then word m0 base (d + 144 * (a - 1) + 8 * q) else initW q

theorem off_add (b : Addr) (x y : Nat) : off b x + BitVec.ofNat 64 y = off b (x + y) := by
  rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem x9_not_pairRegs : Reg.x9 ∉ Reg.x16 :: Reg.x17 :: wRegs := by
  simp only [wRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, reduceCtorEq]
  refine ⟨id, id, ?_⟩
  rintro ⟨q, hq, e⟩
  exact (wReg_ne q hq).2.2.1 e

/-- The pairs `0 … k - 1` of the candidate at `x9 = base + e`, kept where `Z` is set. -/
theorem pairs_ok {s : State} {base : Addr} {size e : Nat} (hs : Scr s base size)
    (h9 : s.gpr .x9 = off base e) (he : e + 144 ≤ size) :
    ∀ k ≤ 9, WP isa (.block ((List.range k).flatMap fun p =>
      [.ldp .x16 .x17 .x9 (16 * p), .cselc .x (accReg (p / 3) (2 * (p % 3))) .x16 (accReg (p / 3) (2 * (p % 3))) .eq,
        .cselc .x (accReg (p / 3) (2 * (p % 3) + 1)) .x17 (accReg (p / 3) (2 * (p % 3) + 1)) .eq])) s
      fun t => t.zf = s.zf ∧ Keeps (.x16 :: .x17 :: wRegs) s t ∧
        ∀ q < 18, t.gpr (wReg q) =
          if q < 2 * k ∧ s.zf then word s.mem base (e + 8 * q) else s.gpr (wReg q) := by
  intro k hk
  refine wp_range_flatMap (M := isa) (N := 9) (fun k t => t.zf = s.zf ∧ Keeps (.x16 :: .x17 :: wRegs) s t ∧
      ∀ q < 18, t.gpr (wReg q) = if q < 2 * k ∧ s.zf then word s.mem base (e + 8 * q) else s.gpr (wReg q))
    (fun p t hp ⟨tz, kt, ta⟩ => ?_) k hk s ?_
  · obtain ⟨r1, r2⟩ := pair_regs p hp
    rw [r1, r2]
    have n1 := wReg_ne (2 * p) (by omega_arith)
    have n2 := wReg_ne (2 * p + 1) (by omega_arith)
    have nx9 : Reg.x9 ∉ Reg.x16 :: Reg.x17 :: wRegs := by
      simp only [wRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, reduceCtorEq]
      refine ⟨id, id, ?_⟩
      rintro ⟨q, hq, e⟩
      exact (wReg_ne q hq).2.2.1 e
    have t9 : t.gpr .x9 = off base e := by rw [kt.gpr _ nx9]; exact h9
    have i1 : InRegions (t.rd ++ t.wr) (t.gpr .x9 + BitVec.ofNat 64 (16 * p)) 8 := by
      rw [t9, off_add, kt.rd, kt.wr]
      have := hs.ld (d := e + 16 * p) (by omega_arith)
      rwa [hs.x0] at this
    have i2 : InRegions (t.rd ++ t.wr) (t.gpr .x9 + BitVec.ofNat 64 (16 * p) + 8) 8 := by
      rw [t9, off_add, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add, kt.rd, kt.wr]
      have := hs.ld (d := e + 16 * p + 8) (by omega_arith)
      rwa [hs.x0] at this
    have h12 : wReg (2 * p) ≠ wReg (2 * p + 1) := fun h => by
      have := wReg_inj _ (by omega_arith) _ (by omega_arith) h; omega_arith
    refine WP.mono (pair_ok h12 ⟨n1.2.2.2.1, n1.2.2.2.2.1⟩ ⟨n2.2.2.2.1, n2.2.2.2.2.1⟩
      ⟨by omega_arith, by omega_arith⟩ i1 i2) fun u ⟨u1, u2, uz, ku⟩ => ?_
    have m : t.mem = s.mem := kt.mem
    refine ⟨uz.trans tz, kt.trans (ku.mono ?_), fun q hq => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_wRegs (by omega_arith)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_wRegs (by omega_arith)))
    · have ta' := ta q hq
      by_cases e1 : q = 2 * p
      · subst e1
        rw [u1, t9, off_add, tz, m, show e + 16 * p = e + 8 * (2 * p) by omega_arith,
          ta (2 * p) hq]
        by_cases hz : s.zf <;> simp [hz, show 2 * p < 2 * (p + 1) by omega_arith]
      · by_cases e2 : q = 2 * p + 1
        · subst e2
          rw [u2, t9, off_add, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add, tz, m,
            show e + 16 * p + 8 = e + 8 * (2 * p + 1) by omega_arith, ta (2 * p + 1) hq]
          by_cases hz : s.zf <;> simp [hz, show 2 * p + 1 < 2 * (p + 1) by omega_arith,
            show ¬ 2 * p + 1 < 2 * p by omega_arith]
        · have nq : wReg q ∉ [Reg.x16, .x17, wReg (2 * p), wReg (2 * p + 1)] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨(wReg_ne q hq).2.2.2.1, (wReg_ne q hq).2.2.2.2.1,
              fun h => e1 (wReg_inj _ hq _ (by omega_arith) h), fun h => e2 (wReg_inj _ hq _ (by omega_arith) h)⟩
          rw [ku.gpr _ nq, ta']
          by_cases hz : s.zf
          · simp only [hz, and_true]
            by_cases hl : q < 2 * p
            · simp [hl, show q < 2 * (p + 1) by omega_arith]
            · simp [hl, show ¬ q < 2 * (p + 1) by omega_arith]
          · simp [hz]
  · exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, fun q _ => by simp⟩

theorem addImm144_ok (s : State) :
    WP isa (.block [.addImm .x .x9 .x9 (24 * K.M.n)]) s fun t =>
      t.gpr .x9 = s.gpr .x9 + BitVec.ofNat 64 144 ∧ Keeps [.x9] s t := by
  apply WP.of_runBlock
  simp only [show 24 * K.M.n = 144 from rfl, runBlock_cons, runStep_some, runBlock_nil,
    exec_addImm_x (show 144 < 4096 by decide), read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

/-- The registers the candidates change. -/
def candRegs : List Reg := .x9 :: .x16 :: .x17 :: wRegs

/-- Candidate `m + 1`, at `d + 144 m`. -/
theorem cand_ok {s : State} {base : Addr} {size d a m : Nat} {m0 : Mem} (hs : Scr s base size)
    (hm : m < 8) (ha : a < 9) (hd : d + 144 * 8 ≤ size) (h9 : s.gpr .x9 = off base (d + 144 * (m - 1)))
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (hmem : s.mem = m0) (hA : Acc m0 base d a m s) :
    WP isa (.block (cand m)) s fun t => Acc m0 base d a (m + 1) t ∧
      t.gpr .x9 = off base (d + 144 * m) ∧ Keeps candRegs s t := by
  rw [cand, List.append_assoc, WP.block_append_iff]
  -- `x9` on to candidate `m + 1`.
  have step : WP isa (.block (if m = 0 then [] else [.addImm .x .x9 .x9 (24 * K.M.n)])) s fun t =>
      t.gpr .x9 = off base (d + 144 * m) ∧ Keeps [.x9] s t := by
    by_cases h0 : m = 0
    · subst h0
      simp only [↓reduceIte]
      exact WP.block_nil ⟨by rw [h9], ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
    · simp only [h0, ↓reduceIte]
      refine WP.mono (addImm144_ok s) fun t ⟨t9, kt⟩ => ⟨?_, kt⟩
      rw [t9, h9, off_add, show d + 144 * (m - 1) + 144 = d + 144 * m by omega_arith]
  refine WP.mono step fun b ⟨b9, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp_ok b ha hm (by rw [kb.gpr _ (by decide)]; exact h2)) fun c ⟨cz, kc⟩ => ?_
  have c9 : c.gpr .x9 = off base (d + 144 * m) := by rw [kc.gpr _ (by decide)]; exact b9
  have hc : Scr c base size := (hs.of_keeps kb (by decide)).of_keeps kc (by decide)
  refine WP.mono (pairs_ok hc c9 (by omega_arith) 9 (Nat.le_refl _)) fun t ⟨tz, kt, ta⟩ => ?_
  have mc : c.mem = m0 := by rw [kc.mem, kb.mem, hmem]
  refine ⟨fun q hq => ?_, ?_, ?_⟩
  · have hq' : ¬ (wReg q = .x9 ∨ wReg q = .x16) := fun h =>
      h.elim (wReg_ne q hq).2.2.1 (wReg_ne q hq).2.2.2.1
    rw [ta q hq, cz, mc, kc.gpr _ (by simpa using (wReg_ne q hq).2.2.2.1),
      kb.gpr _ (by simpa using (wReg_ne q hq).2.2.1), hA q hq]
    by_cases e : a = m + 1
    · subst e
      simp [hq, show d + 144 * m + 8 * q = d + 144 * (m + 1 - 1) + 8 * q by omega_arith]
    · have : (1 ≤ a ∧ a ≤ m + 1) ↔ (1 ≤ a ∧ a ≤ m) := by omega_arith
      simp [e, this]
  · rw [kt.gpr _ x9_not_pairRegs]; exact c9
  · refine ((kb.mono ?_).trans (kc.mono ?_)).trans (kt.mono ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [candRegs]
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [candRegs]
    · intro r hr; exact List.mem_cons_of_mem _ hr

/-- The eight candidates. -/
theorem scan_ok {s : State} {base : Addr} {size d a : Nat} (hs : Scr s base size)
    (ha : a < 9) (hd : d + 144 * 8 ≤ size) (h9 : s.gpr .x9 = off base d)
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (hA : Acc s.mem base d a 0 s) :
    WP isa (.block ((List.range 8).flatMap cand)) s fun t => Acc s.mem base d a 8 t ∧ Keeps candRegs s t := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) (fun n t => Acc s.mem base d a n t ∧
      t.gpr .x9 = off base (d + 144 * (n - 1)) ∧ Keeps candRegs s t)
    (fun m t hm ⟨tA, t9, kt⟩ => ?_) 8 (Nat.le_refl _) s ⟨hA, by rw [h9]; simp, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩)
    fun t ⟨tA, _, kt⟩ => ⟨tA, kt⟩
  have n2 : Reg.x2 ∉ candRegs := by
    simp only [candRegs, wRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, reduceCtorEq]
    refine ⟨id, id, id, ?_⟩
    rintro ⟨q, hq, e⟩
    exact (wReg_ne q hq).2.1 e
  refine WP.mono (cand_ok (hs.of_keeps kt (by decide)) hm ha hd t9 (by rw [kt.gpr _ n2]; exact h2) kt.mem tA)
    fun u ⟨uA, u9, ku⟩ => ⟨uA, by rw [u9, Nat.add_sub_cancel], kt.trans ku⟩

/-- `x9` = the table's address. -/
theorem tblBase_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    WP isa (.block tblBase) s fun t => t.gpr .x9 = off base K.tbl ∧ Keeps [.x9] s t := by
  apply WP.of_runBlock
  simp only [tblBase, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, hs.x0, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem init_regs : (∀ q < 18, q / 6 ≠ 1 → wReg q ∈ Impl.P384.EcdhSelect.acc 0 ++ Impl.P384.EcdhSelect.acc 2) ∧
    (∀ q < 18, q / 6 = 1 → wReg q = accReg 1 (q % 6)) ∧ (∀ w < 6, accReg 1 w ∉ Impl.P384.EcdhSelect.acc 0 ++ Impl.P384.EcdhSelect.acc 2) ∧
    (∀ r ∈ Impl.P384.EcdhSelect.acc 0 ++ Impl.P384.EcdhSelect.acc 2, r ∈ wRegs) ∧ (∀ w < 6, accReg 1 w ∈ wRegs) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro r hr
    simp only [Impl.P384.EcdhSelect.acc, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_wRegs (q := 0) (by decide)
    · exact mem_wRegs (q := 1) (by decide)
    · exact mem_wRegs (q := 2) (by decide)
    · exact mem_wRegs (q := 3) (by decide)
    · exact mem_wRegs (q := 4) (by decide)
    · exact mem_wRegs (q := 5) (by decide)
    · exact mem_wRegs (q := 12) (by decide)
    · exact mem_wRegs (q := 13) (by decide)
    · exact mem_wRegs (q := 14) (by decide)
    · exact mem_wRegs (q := 15) (by decide)
    · exact mem_wRegs (q := 16) (by decide)
    · exact mem_wRegs (q := 17) (by decide)
  · intro w hw
    have : accReg 1 w = wReg (6 + w) := by
      unfold wReg; rw [show (6 + w) / 6 = 1 by omega_arith, show (6 + w) % 6 = w by omega_arith]
    rw [this]; exact mem_wRegs (by omega_arith)

/-- `(0 : R : 0)` in the accumulators. -/
theorem init_ok (s : State) (m0 : Mem) (base : Addr) (d a : Nat) :
    WP isa (.block init) s fun t => Acc m0 base d a 0 t ∧ Keeps wRegs s t := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := init_regs
  rw [init, WP.block_append_iff]
  refine WP.mono (zeros_ok s _) fun b ⟨bz, kb⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 6) (fun k t =>
      (∀ w < k, t.gpr (accReg 1 w) = wordOf K.one w) ∧ Keeps ((List.range 6).map (accReg 1)) b t)
    (fun w t hw ⟨tw, kt⟩ => ?_) 6 (Nat.le_refl _) b
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩) fun t ⟨tw, kt⟩ => ?_
  · refine WP.mono (const64_ok t (accReg 1 w) (wordOf K.one w)) fun u ⟨u1, ku⟩ => ⟨fun w' hw' => ?_,
      kt.trans (ku.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)⟩
    by_cases e : w' = w
    · subst e; exact u1
    · have : accReg 1 w' ≠ accReg 1 w := by
        have := (show ∀ i < 6, ∀ j < 6, accReg 1 i = accReg 1 j → i = j by decide) w' (by omega_arith) w hw
        exact fun h => e (this h)
      rw [ku.gpr _ (by simpa using this)]
      exact tw w' (by omega_arith)
  · refine ⟨fun q hq => ?_, (kb.mono i4).trans (kt.mono fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact i5 w (List.mem_range.mp hw))⟩
    have h0 : ¬ (1 ≤ a ∧ a ≤ 0) := by omega_arith
    simp only [h0, ↓reduceIte, initW]
    by_cases h1 : q / 6 = 1
    · simp only [h1, ↓reduceIte]
      rw [i2 q hq h1]; exact tw _ (Nat.mod_lt _ (by decide))
    · simp only [h1, ↓reduceIte]
      have hm := i1 q hq h1
      rw [kt.gpr _ (fun h => by
        obtain ⟨w, hw, e⟩ := List.mem_map.mp h
        exact i3 w (List.mem_range.mp hw) (e ▸ hm))]
      exact bz _ hm

theorem acc_words : ∀ c < 3, ∀ j < 6, (Impl.P384.EcdhSelect.acc c)[j]? = some (wReg (6 * c + j)) := by
  decide

theorem acc_len (c : Nat) : (Impl.P384.EcdhSelect.acc c).length = 6 := by
  unfold Impl.P384.EcdhSelect.acc; split <;> rfl

theorem acc_nodup : ∀ c < 3, (Impl.P384.EcdhSelect.acc c).Nodup := by decide

theorem acc1_eq : Impl.P384.EcdhSelect.acc 1 = (List.range' 0 6).map (accReg 1) := rfl

theorem sel_regs : (∀ r ∈ (.x2 :: .x3 :: .x4 :: .x9 :: .x16 :: candRegs : List Reg), r ∈ combClob K.M.n) ∧
    Reg.x0 ∉ (.x2 :: .x3 :: .x4 :: .x9 :: .x16 :: candRegs : List Reg) ∧
    Reg.x19 ∉ (.x2 :: .x3 :: .x4 :: .x9 :: .x16 :: candRegs : List Reg) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The accumulators of coordinate `c` stored at `o`: the entry's coordinate, or `(0 : R : 0)`'s. -/
theorem coord_val {u : State} {m0 : Mem} {base : Addr} {a c : Nat} (hc : c < 3) (ha : a ≤ 8)
    (hA : Acc m0 base K.tbl a 8 u) :
    regsVal u (Impl.P384.EcdhSelect.acc c) = if a = 0 then (if c = 1 then K.one else 0) else
      wordsVal m0 base (tblSlot K c (a - 1)) K.M.n := by
  by_cases h0 : a = 0
  · subst h0
    simp only [↓reduceIte]
    have hz : ∀ j < 6, u.gpr (wReg (6 * c + j)) = initW (6 * c + j) := fun j hj => by
      rw [hA _ (by omega_arith)]; simp
    by_cases h1 : c = 1
    · subst h1
      simp only [↓reduceIte]
      rw [acc1_eq]
      refine Mont.regsVal_of_shifts u (accReg 1) 0 6 K.one (by decide) fun k hk => ?_
      have := hz k hk
      simp only [initW, show (6 * 1 + k) / 6 = 1 by omega_arith, show (6 * 1 + k) % 6 = k by omega_arith,
        ↓reduceIte] at this
      rw [Nat.zero_add, show accReg 1 k = wReg (6 * 1 + k) by
        unfold wReg; rw [show (6 * 1 + k) / 6 = 1 by omega_arith, show (6 * 1 + k) % 6 = k by omega_arith], this]
      rfl
    · simp only [h1, ↓reduceIte]
      refine regsVal_eq_zero fun r hr => ?_
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
      have hj6 : j < 6 := by
        have := (List.getElem?_eq_some_iff.mp hj).1; rwa [acc_len] at this
      rw [acc_words c hc j hj6] at hj
      cases hj
      rw [hz j hj6]
      simp [initW, show (6 * c + j) / 6 = c by omega_arith, h1]
  · simp only [h0, ↓reduceIte]
    rw [Mont.regsVal_of_loads (mem := m0) (p := base) _ (tblSlot K c (a - 1)) ?_, acc_len]
    · rfl
    intro j r hr
    have hj6 : j < 6 := by
      have := (List.getElem?_eq_some_iff.mp hr).1; rwa [acc_len] at this
    rw [acc_words c hc j hj6] at hr
    cases hr
    have hc' : 1 ≤ a ∧ a ≤ 8 := ⟨by omega_arith, ha⟩
    rw [hA _ (by omega_arith), tblSlot_eq]
    simp only [hc', and_self, ↓reduceIte]
    congr 1
    show K.tbl + 144 * (a - 1) + 8 * (6 * c + j) = K.tbl + 8 * 6 * (3 * (a - 1) + c) + 8 * j
    omega_arith

/-- P-384's selection does what the window's must. -/
theorem sel_ok : SelOk K 8192 (WinCfg.selOf K (some sel)) := by
  intro base k i s hL hA hs hi hx hbits
  have hn := hs.nowrap
  have hmag := mag_le (nib_lt k i)
  show WP isa (.block sel) s _
  simp only [Impl.P384.EcdhSelect.sel, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (nibble_ok hs K.bits (k := k) (j := i) (N := 4 * K.J) (by omega_arith) hL.bits hA.bits4 hx hbits)
    fun s₁ ⟨a₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok s₁ (nib_lt k i) a₁) fun s₂ ⟨a₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tblBase_ok hs₂) fun s₃ ⟨b₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (init_ok s₃ s₃.mem base K.tbl (mag (nib k i))) fun s₄ ⟨A₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have m₄ : s₄.mem = s₃.mem := k₄.mem
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (mag (nib k i)) := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide)]; exact a₂
  have x9₄ : s₄.gpr .x9 = off base K.tbl := by rw [k₄.gpr _ (by decide)]; exact b₃
  rw [WP.block_append_iff]
  refine WP.mono (scan_ok hs₄ (by omega_arith) (by decide) x9₄ x2₄ (m₄ ▸ A₄)) fun s₅ ⟨A₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have m₅ : s₅.mem = s.mem := by rw [k₅.mem, m₄, k₃.mem, k₂.mem, k₁.mem]
  rw [m₄, k₃.mem, k₂.mem, k₁.mem] at A₅
  -- The stores.
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok _ hs₅ (o := K.E.x) (by rw [acc_len]; decide) (by decide) (acc_nodup 0 (by decide)))
    fun s₆ ⟨v₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok _ hs₆ (o := K.E.y) (by rw [acc_len]; decide) (by decide) (acc_nodup 1 (by decide)))
    fun s₇ ⟨v₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  refine WP.mono (stores_ok _ hs₇ (o := K.E.z) (by rw [acc_len]; decide) (by decide) (acc_nodup 2 (by decide)))
    fun t ⟨v₈, k₈, O₈⟩ => ?_
  obtain ⟨cR, c0, c19⟩ := sel_regs
  have kk : Keeps (.x2 :: .x3 :: .x4 :: .x9 :: .x16 :: candRegs) s s₅ :=
    ((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      (k₄.mono fun r hr => by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))))))).trans
      (k₅.mono fun r hr => by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))
  have g : ∀ r, t.gpr r = s₅.gpr r := fun r => by
    rw [k₈.gpr r (by simp), k₇.gpr r (by simp), k₆.gpr r (by simp)]
  have r₅ : ∀ c, regsVal s₇ (Impl.P384.EcdhSelect.acc c) = regsVal s₅ (Impl.P384.EcdhSelect.acc c) ∧
      regsVal s₆ (Impl.P384.EcdhSelect.acc c) = regsVal s₅ (Impl.P384.EcdhSelect.acc c) := fun c =>
    ⟨regsVal_congr fun r _ => by rw [k₇.gpr r (by simp), k₆.gpr r (by simp)],
      regsVal_congr fun r _ => by rw [k₆.gpr r (by simp)]⟩
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, by rw [g, kk.gpr _ c0], by rw [g, kk.gpr _ c19], ?_, ?_, ?_, ?_⟩
  · rw [g, kk.gpr r fun h => hr (cR r h)]
  · rw [k₈.rd, k₇.rd, k₆.rd, kk.rd]
  · rw [k₈.wr, k₇.wr, k₆.wr, kk.wr]
  · rw [k₈.sp, k₇.sp, k₆.sp, kk.sp]
  · rw [acc_len] at O₆ O₇ O₈
    rw [← m₅]; exact (O₆.unch.trans (O₇.unch.trans O₈.unch)).mono (by decide)
  · rw [acc_len] at O₇ O₈ v₆
    rw [O₈.wordsVal (by decide) (by decide), O₇.wordsVal (by decide) (by decide)]
    show wordsVal s₆.mem base K.E.x 6 = _
    rw [v₆, coord_val (c := 0) (by decide) hmag A₅]
    simp
  · rw [acc_len] at O₈ v₇
    rw [O₈.wordsVal (by decide) (by decide)]
    show wordsVal s₇.mem base K.E.y 6 = _
    rw [v₇, (r₅ 1).2, coord_val (c := 1) (by decide) hmag A₅]
    simp
  · rw [acc_len] at v₈
    show wordsVal t.mem base K.E.z 6 = _
    rw [v₈, (r₅ 2).1, coord_val (c := 2) (by decide) hmag A₅]
    simp

end VG.Proof.P384.EcdhSelect

end

end

/-! ### `P384.EcdhMadd`, which only this module used -/

section

/-!
# P-384's inline mixed addition

`madd_ok`: the inline mixed addition (`Impl/P384/EcdhMadd.lean`) does what
the window's must (`MaddSpec`), as `ofN_ok` shows of the field program's: its
operations are `fprog_ok`'s, on the slots the field program uses.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhMadd
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Impl.P384.EcdhMadd
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

/-- The inline mixed addition, as the window's. -/
theorem madd_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) : MaddSpec K C base size (.block madd) := by
  intro E s hI
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have hAp := hL.rcbApart_D (Or.inr rfl)
  rw [madd, maddJ_eq]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp _ hI (fun op hop x hx => w1.1 x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk maddJN_ok _ _ _ _) fun x hx => hx)) fun s' ⟨k, I⟩ => ?_
  have hw : ∀ w ∈ (ofN maddJN K.S K.R K.E K.D).map FOp.out, w ∈ rcbW K.S K.D := fun w hw => by
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  refine ⟨⟨fun r hr => k.gpr r fun h => hr (by
      have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
      exact this r h), k.rd, k.wr, k.sp⟩,
    (ProgKeepX.mono k hw).unch.mono fun w hw => ?_, _, I.sub fun x hx => ?_,
    fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out maddJN_ok op hop),
    (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 7) (ofN_run maddJN_ok hAp E 8))).trans (maddJN_run _)⟩
  · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, w1.2.1 y hy, rfl⟩
    · exact Or.inr rfl
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx

/-- P-384's inline mixed addition, as the window's. -/
theorem maddOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) : MaddOk K C base 8192 (some (.block madd)) := by
  intro m hm
  cases hm
  exact madd_ok hC hL hA hp

end VG.Proof.P384.EcdhMadd

end

end

/-!
# ECDH over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `invSound_of_toM`), and of prime order
(`Proof.P384.primeOrder`), so the windows with a Jacobian accumulator compute `[d]P` (`mulJ4_ok`) and
`exchangeWith_ok'` gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p384 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p384 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  dsimp only [ecdhAArch64]
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p384.C (dk p384 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p384.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP384 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-384's
  -- terms before the literals' facts are known.
  have ha : AbiOk exchangeP384 := by lit_decide
  have hmc : CallsKeep (Impl.Ecdh.AArch64.Cfg.middle p384) :=
    callsKeep_ofK (c := Impl.Ecdh.AArch64.Cfg.middle p384) (by lit_decide)
  have hmu : KeepsUntouched (Impl.Ecdh.AArch64.Cfg.middle p384) :=
    keepsUntouched_ofK (c := Impl.Ecdh.AArch64.Cfg.middle p384) (by lit_decide)
  have hm : Ecdh.AArch64.MulOk p384 (Cfg.mulJ4 p384
      (some (.block Impl.P384.EcdhAllocatedCode.doubleRD, .block Impl.P384.EcdhAllocatedCode.doubleDR))
      (some (.block Impl.P384.EcdhMadd.madd)) (some Impl.P384.EcdhSelect.sel)) :=
    Ecdh.AArch64.mulJ4_ok (p384_ok hI) hL hO rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI)) (Ecdh.AArch64.winAQ (p384_ok hI))
        (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      (P384.EcdhMadd.maddOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
        (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      P384.EcdhSelect.sel_ok
  obtain ⟨t, s', he, hsv, -, hpost⟩ :=
    Ecdh.AArch64.exchangeWith_ok' (p384_ok hI) hL hm (by decide +kernel) hmc hmu (pre_of hs)
  exact ⟨t, s', he, abiPreserved_ofK he ha hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    Verified AArch64.target exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI hO) ecdh_ct implies

end VG.Proof.Ecdh.AArch64.P384
