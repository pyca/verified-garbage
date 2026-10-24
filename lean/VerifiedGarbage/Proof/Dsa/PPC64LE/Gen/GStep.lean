module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GPow
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.GCmp
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSLoad
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSSetup
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: one `h` of the generator search

`gStep` (`gStep_vp`): `h`, the `pLen` bytes at `fH` of the `hs` tape, into
array `aH` of the key working space (zeroed first); unless `1 < h < p − 1`,
nothing more; else `g = h^((p−1)/q) mod p` by the power in the P space, and
if `g > 1`, `g` big-endian at `sG` and `fG` := 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 stBorrow andS)
open VG.Proof.Mont (off)

/-- The `h` at byte `i` of the tape. -/
abbrev hAt (G : GP) (i : Nat) : List Byte := (G.hsB.drop i).take G.pLen

section
variable {G : GP} {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat}

theorem GI.hsFit (h : GI G STK σ V LS s) : G.hs.toNat + G.hsLen ≤ 2 ^ 64 := by
  have := h.pre.nH; rw [← h.hG]; exact this

/-- The tape is apart from what the search changes. -/
theorem GI.hs_apart (h : GI G STK σ V LS s) : ∀ r ∈ [G.rScr, rBelow σ STK], G.rHs.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← h.hG]; exact h.pre.hC
  · rw [← h.hG]; exact h.pre.bH.symm

/-- The `h` at byte `i`, in memory. -/
theorem GI.hBytes (h : GI G STK σ V LS s) {i : Nat} (hi : i + G.pLen ≤ G.hsLen) :
    Spec.Rsa.bytesAt s.mem (G.hs + BitVec.ofNat 64 i) G.pLen = hAt G i := by
  have fit := h.hsFit
  have hw : Spec.Rsa.bytesAt s.mem G.hs G.hsLen = G.hsB := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt h.frame h.hs_apart (by omega), ← h.hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.hsLen = i + G.pLen + d := ⟨G.hsLen - i - G.pLen, by omega⟩
  show _ = (G.hsB.drop i).take G.pLen
  rw [← hw, hd, VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.append_assoc, List.drop_left' (by simp [Spec.Rsa.bytesAt]),
    List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The `h` at byte `i`, as a source of a load. -/
theorem GI.hSrc (h : GI G STK σ V LS s) {i : Nat} (hi : i + G.pLen ≤ G.hsLen) (hp : 0 < G.pLen) :
    Covers [⟨G.hs + BitVec.ofNat 64 i, G.pLen⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨G.hs + BitVec.ofNat 64 i, G.pLen⟩ G.rScr ∧
      (G.hs + BitVec.ofNat 64 i).toNat + G.pLen ≤ 2 ^ 64 ∧
      Spec.Rsa.bytesAt s.mem (G.hs + BitVec.ofNat 64 i) G.pLen = hAt G i := by
  have fit := h.hsFit
  have sub : Region.Sub ⟨G.hs + BitVec.ofNat 64 i, G.pLen⟩ G.rHs := Offset.sub_base _ hi
  have hC := h.pre.hC; rw [h.hG] at hC
  refine ⟨Covers.left (Covers.one ⟨G.rHs, by rw [h.rd, h.pre.rd, h.hG]; simp,
    Offset.contains_base _ hi (by omega)⟩), hC.sub_left sub, ?_, h.hBytes hi⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The bytes of a covered region, one by one. -/
theorem covers_bytes {rs : List Region} {P : Addr} {n : Nat} (hc : Covers [⟨P, n⟩] rs)
    (hfit : P.toNat + n ≤ 2 ^ 64) : ∀ i < n, InRegions rs (off P i) 1 := fun i hi =>
  hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (show i + 1 ≤ n by omega) (by omega)⟩

end

/-- The stage after an `h` (`hv`), from `p` (`pv`) and `(p − 1) / q` (`ev`). -/
def gOut (c : Cfg) (G : GP) (hv pv ev : Nat) : Cfg :=
  if 1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv then
    ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1
  else c

/-- Simplifies the arrays and key header words of `gStep`'s stages. -/
syntax "g_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| g_simp $[$loc]?) => `(tactic| simp only [KU, VG.Proof.Rsa.KeyWorkspace.upd, aPm1, aH, aOne,
    aZero, aTmp, slLo, slHi, Nat.reduceEqDiff, ↓reduceIte] $[$loc]?)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `h`'s pointer and its length, in the key working space. -/
theorem hPtrK_vp {H : Addr} (hH : fH ∈ c.LS) (hHv : c.V fH = H) :
    VP (KSt G c X) (.block [ld .r6 fH, .li .r8 G.pLen])
      (fun σ s => KSt G c X σ s ∧ s.gpr .r6 = H ∧ s.gpr .r8 = BitVec.ofNat 64 G.pLen) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block [ld .r6 fH, .li .r8 G.pLen]), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have l := h.lens
  have hE := h.gi.hEnd_le
  have p15 : G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine WP.cons (s' := s.write .r6 H) ?_ (WP.cons (s' := (s.write .r6 H).write .r8 (BitVec.ofNat 64 G.pLen))
    (exec_li p15) (WP.block_nil ?_))
  · rw [show ld .r6 fH = .load .d .r6 .r28 fH from rfl, exec_load_d (by decide) ⟨by decide, by decide⟩
      (by rw [h.gi.r28]; exact h.gi.inRdWr (by simp only [hEnd, fSave, fH] at hE ⊢; omega)), h.gi.r28,
      show s.mem.readW (G.scr + BitVec.ofNat 64 fH) 64 = H from (h.gi.slotV hH).trans hHv]
  have k : BKeep [.r6, .r8] s ((s.write .r6 H).write .r8 (BitVec.ofNat 64 G.pLen)) :=
    (VG.Proof.Bignum.PPC64LE.Keep.write s .r6 H).trans (VG.Proof.Bignum.PPC64LE.Keep.write _ .r8 _)
  refine ⟨⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ rfl k.sp, x⟩, kr.of_keep ⟨k.gpr, k.rd, k.wr⟩⟩, ?_, (Upd.write _ _ _).gpr⟩
  rw [(Upd.write _ .r8 _).other .r6 (by decide), (Upd.write _ _ _).gpr]

/-- A stage with more arrays than `c₀` and the same header words and claims is `c₀`'s. -/
theorem SS.back {σ s : State} {c' c₀ : Cfg} (h : SS G 176 σ c' s) (hk : c₀.kls = []) (eV : c'.V = c₀.V)
    (eLS : c'.LS = c₀.LS) (ecl : c'.cl = c₀.cl) (eA : ∀ j ∈ c₀.live, j ∈ c'.live ∧ c'.A j = c₀.A j) :
    SS G 176 σ c₀ s :=
  h.mono (fun o ho => ⟨eLS ▸ ho, by rw [eV]⟩) (fun y hy => ecl ▸ hy) eA (fun d hd => by simp [hk] at hd)

theorem beq_zero_of_iff {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) : (x == 0) = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]; exact beq_iff_eq.mpr (h.mpr hp)
  · rw [decide_eq_false hp]; exact beq_false_of_ne fun e => hp (h.mp e)

theorem ite01_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0) = 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite01_le (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  by_cases hp : p <;> simp [hp]

/-- One `h` (the `pLen` bytes at byte `i` of the tape, which `fH` points at):
the stage `gOut`. -/
theorem gStep_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {pv ev i : Nat} (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hZ : aZero ∈ c.live) (hZv : c.A aZero = 0) (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hkls : c.kls = [])
    (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x ∧ Apart sG G.pLen x)
    (hH : fH ∈ c.LS) (hHv : c.V fH = G.hs + BitVec.ofNat 64 i) (hi : i + G.pLen ≤ G.hsLen) :
    VP (St G c X) g.gStep (St G (gOut c G (Spec.Dsa.decodeBE (hAt G i)) pv ev) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  unfold Geo.gStep
  rw [hg, hgq]
  have hplt : pv < 2 ^ (8 * G.pLen) := by rwa [Nat.pow_mul]
  generalize hhv : Spec.Dsa.decodeBE (hAt G i) = hv
  have eos : Spec.Rsa.os2ip (hAt G i) = hv := hhv
  have kc : ∀ (v : Nat), ∀ j ∈ c.live, j ∈ aH :: aH :: c.live ∧ KU (KU c.A aH (c.A aZero)) aH v j = c.A j :=
    fun v j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj), by
      have : j ≠ aH := fun e => hHl (e ▸ hj)
      show VG.Proof.Rsa.KeyWorkspace.upd (VG.Proof.Rsa.KeyWorkspace.upd c.A aH _) aH v j = _
      rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ this, VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ this]⟩
  -- Into the key working space; `aH` := 0, then `h`.
  refine VP.seq ksEnter_vp ?_
  refine VP.seq (copy_vp (o := aH) (a := aZero) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28, .r29, .r30, .r31]) (copy aH aZero), rfl⟩ (by decide) hZ (by decide)) ?_
  refine VP.seq (hPtrK_vp hH hHv) ?_
  refine VP.seq (loadZ_vp (j := aH) (n := G.pLen) (bs := hAt G i) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8]) (VG.Impl.Rsa.PPC64LE.CrtValues.load aH), rfl⟩
    (by decide) List.mem_cons_self (by g_simp; exact hZv)
    (by rcases l with e | e | e <;> rw [e] <;> decide)
    (by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide) fun σ s h => ?_) ?_
  · obtain ⟨cov, dj, _, b⟩ := h.1.gi.hSrc hi (by rcases l with e | e | e <;> rw [e] <;> decide)
    exact ⟨cov, dj.sub_right h.1.gi.kSub, b⟩
  rw [hhv]
  -- `1 < h`, `h < p − 1` and both.
  refine VP.seq (ltS_vp (d := slLo) (a := aOne) (b := aH) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31]) (sub3 aTmp aOne aH), rfl⟩
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31]) (.block (stBorrow slLo)), rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hTl⟩) ⟨by decide, by decide⟩) ?_
  refine VP.seq (ltS_vp (d := slHi) (a := aH) (b := aPm1) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31]) (sub3 aTmp aH aPm1), rfl⟩
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31]) (.block (stBorrow slHi)), rfl⟩
    (by simp) (by simp [hM]) (by decide) (by decide)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hTl⟩) ⟨by decide, by decide⟩) ?_
  refine VP.seq (andCmp_vp (d := slLo) (a := slLo) (b := slHi) ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r29, .r30, .r31])
      (.block (andS slLo slLo slHi ++ ([.load .w .r0 .r31 slLo] : List Instr))), rfl⟩
    ⟨by decide, by decide⟩ (by simp) (by simp) (by g_simp; exact ite01_le _) (by g_simp; exact ite01_le _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- Out of range: nothing more.
    refine VP.block_nil fun σ s ⟨⟨⟨⟨h, x⟩, _⟩, e⟩, z⟩ => ⟨?_, x⟩
    rw [e] at z
    have nr : ¬(1 < hv ∧ hv < pv - 1) := by
      intro hr; simp only [Option.some.injEq, decide_eq_true_eq] at z
      g_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact z ⟨(ite01_eq_one _).mpr hr.1, (ite01_eq_one _).mpr hr.2⟩
    have nc : ¬(1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv) := fun hc => nr ⟨hc.1, hc.2.1⟩
    simp only [gOut, nc, ↓reduceIte]
    exact h.back hkls rfl rfl rfl (kc hv)
  · by_cases hr : 1 < hv ∧ hv < pv - 1
    swap
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at z
      g_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact hr ⟨(ite01_eq_one _).mp z.1, (ite01_eq_one _).mp z.2⟩
    have eq : gOut c G hv pv ev = if 1 < hv ^ ev % pv then
        ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1 else c := by
      simp only [gOut, hr, true_and]
    rw [eq]
    generalize hgv : hv ^ ev % pv = gv
    have glt : gv < pv := hgv ▸ Nat.mod_lt _ (by omega)
    -- `g`, back at the stage `c`.
    refine VP.seq ((power_vp (c := c) (X := X) (H := G.hs + BitVec.ofNat 64 i) (hb := hAt G i) cert hPc hpv hp2
      hpo hEc hev hH hHv (fun x hx => (hcl x hx).1) fun σ s h => ?_).mono
      (fun σ s ⟨⟨⟨⟨h, x⟩, _⟩, _⟩, _⟩ => ⟨h.back hkls rfl rfl rfl (kc hv), x⟩)
      (G' := fun σ t => St G c X σ t ∧ VG.Proof.MillerRabin.PPC64LE.Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
        VG.Proof.MillerRabin.PPC64LE.arr t.mem G.pS (pw G.pLen) 4 = gv ∧ (t.gpr .r0 = 0 ↔ 1 < gv ∧ gv < pv))
      fun σ t ⟨h, en, v4, r0⟩ => ⟨h, en, by rw [v4, eos, hgv], by rw [← hgv, ← eos, ← v4]; exact r0⟩) ?_
    · obtain ⟨cov, dj, fit, b⟩ := h.1.gi.hSrc hi (by rcases l with e | e | e <;> rw [e] <;> decide)
      exact ⟨covers_bytes cov fit, dj, fit, b⟩
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [eval_zero, eval_zero, beq_zero_of_iff h₁.2.2.2, beq_zero_of_iff h₂.2.2.2]) ?_ ?_
    · -- 1 < g: stored.
      by_cases h1 : 1 < gv
      · simp only [h1, ↓reduceIte]
        exact (gOut_vp (c := c) (g := gv) (by omega) fun x hx => (hcl x hx).2).mono
          (fun σ s ⟨⟨h, en, v4, _⟩, _⟩ => ⟨h, en, v4⟩) fun _ _ h => h
      · refine VP.of_false fun σ s ⟨⟨_, _, _, r0⟩, z⟩ => h1 ?_
        rw [eval_zero, beq_zero_of_iff r0] at z
        simp only [Option.some.injEq, decide_eq_true_eq] at z
        exact z.1
    · by_cases h1 : 1 < gv
      · refine VP.of_false fun σ s ⟨⟨_, _, _, r0⟩, z⟩ => ?_
        rw [eval_zero, beq_zero_of_iff r0] at z
        simp only [Option.some.injEq, decide_eq_false_iff_not] at z
        exact z ⟨h1, glt⟩
      · simp only [h1, ↓reduceIte]
        exact VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => h

end

end VG.Proof.Dsa.PPC64LE.Gen
