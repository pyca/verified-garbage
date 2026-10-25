module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GPow
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GCopy
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GCmp
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PArith
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Tape
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: one `h` of the generator search

`gStep` (`gStep_vp`): `h`, the `pLen` bytes at `fH` of the `hs` tape, into
array `aH`; unless `1 < h < p − 1`, nothing more; else `g = h^((p−1)/q) mod p`
by the exponentiation, and if `g > 1`, `g` big-endian at `sG` and `fG` := 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_movw)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Proof.Rsa (b2n)

/-- The `h` at byte `i` of the tape. -/
abbrev hAt (G : GP) (i : Nat) : List Byte := (G.hsB.drop i).take G.pLen

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

theorem GI.hsFit (h : GI G σ V LS s) : G.hs.toNat + G.hsLen ≤ 2 ^ 32 := by
  have := h.pre.nH; rw [← h.hG]; exact this

/-- The `h` at byte `i`, as a source of a load. -/
theorem GI.hSrc (h : GI G σ V LS s) {i : Nat} (hi : i + G.pLen ≤ G.hsLen) (hp : 0 < G.pLen) :
    Covers [⟨State.addr (G.hs + BitVec.ofNat 32 i), G.pLen⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨State.addr (G.hs + BitVec.ofNat 32 i), G.pLen⟩ G.rK ∧
      (G.hs + BitVec.ofNat 32 i).toNat + G.pLen ≤ 2 ^ 32 ∧
      Spec.Rsa.bytesAt s.mem (State.addr (G.hs + BitVec.ofNat 32 i)) G.pLen = hAt G i := by
  have fit := h.hsFit
  have a : State.addr (G.hs + BitVec.ofNat 32 i) = State.addr G.hs + BitVec.ofNat 64 i := addr_add (by omega_arith)
  have sub : Region.Sub ⟨State.addr G.hs + BitVec.ofNat 64 i, G.pLen⟩ G.rHs := Offset.sub_base _ hi
  have hC := h.pre.hC; rw [h.hG] at hC
  have e : G.hsB = Spec.Rsa.bytesAt σ.mem (State.addr G.hs) G.hsLen := by rw [← h.hG]; rfl
  refine ⟨Covers.left (Covers.one ⟨G.rHs, by rw [h.rd, h.pre.rd, h.hG]; simp, a ▸ Offset.contains_base _ hi
    (by omega_arith)⟩), a ▸ (hC.sub_left sub).sub_right h.kSub, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [h.keeps fit h.hs_apart hi, hAt, e]

end

/-- The stage after an `h` (`hv`), from `p` (`pv`) and `(p − 1) / q` (`ev`). -/
def gOut (c : Cfg) (G : GP) (hv pv ev : Nat) : Cfg :=
  if 1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv then
    ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1
  else c

/-- The certificates of `gStep`'s pieces that depend on the geometry. -/
structure GStepCerts (g : Geo) : Prop where
  mod : Cert7 (copyN (scr g.pLen .r0 (sA + g.powMod)) (ptr .r1 aP) g.pLen)
  base : Cert7 (copyN (scr g.pLen .r0 (sA + g.powBase)) (ptr .r1 aH) g.pLen)
  exp : Cert7 (copyN (scr g.pLen .r0 (sA + g.powExp)) (ptr .r1 aE) (4 * g.e))
  res : Cert7 (copyN (ptr .r0 aG) (scr g.pLen .r1 (sA + g.powRes)) g.pLen)
  st : Cert7 (storeBE g.pLen aG sG g.pLen)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Simplifies a stage's arrays and header words. -/
syntax "kv_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| kv_simp $[$loc]?) => `(tactic| simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, aQt, aRm, aDv, aDt,
    aX, aT, aS, aPm1, aP, aE, aH, aOne, aG, aZero, aTmp, slOdd, slLo, slHi, slG, Nat.reduceEqDiff, ↓reduceIte] $[$loc]?)

/-- `scratch` below the key working space lies in the 32-bit address space. -/
abbrev Fit (G : GP) : Prop := sK G.pLen ≤ 2 ^ 32

theorem SS.fit {σ s : State} (h : SS G σ c s) : Fit G := by
  have := h.gi.scrBig; have := h.gi.scrFit; simp only [Fit]; omega_arith

/-- A range of `scratch` through a copy to another. -/
theorem scr_keep {m m' : Mem} {a n b k : Nat} (fit : Fit G) (f : Frame [G.rs a n] m m')
    (hs : b + k ≤ a ∨ a + n ≤ b) (ha : a + n ≤ sK G.pLen) (hb : b + k ≤ sK G.pLen) :
    m'.read (G.sa b) k = m.read (G.sa b) k := by
  simp only [Fit] at fit
  exact f.read (r := G.rs b k) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ hs (by omega_arith) (by omega_arith)) (by omega_arith)

/-- `g` from `h` (`hv`) in range: `h ^ ((p − 1) / q) mod p`, stored if it is
above 1. The stage `c` is `c0`'s with more arrays and header words. -/
theorem gPow_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {c0 : Cfg} {pv ev hv : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hHm : aH ∈ c.live) (hHv : c.A aH = hv) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hTl : aTmp ∉ c.live) (hGl : aG ∉ c0.live)
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hvlt : hv < 2 ^ (8 * G.pLen)) (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG)
    (eV : c.V = c0.V) (eLS : c.LS = c0.LS) (ecl : c.cl = c0.cl)
    (eA : ∀ j ∈ c0.live, j ∈ c.live ∧ c.A j = c0.A j) (ek : c0.kls = []) :
    VP (St G c X)
      (VG.Impl.Rsa.Arm.Keys.seqs [copyN (scr G.pLen .r0 (sA + g.powMod)) (ptr .r1 aP) G.pLen,
        copyN (scr G.pLen .r0 (sA + g.powBase)) (ptr .r1 aH) G.pLen,
        copyN (scr G.pLen .r0 (sA + g.powExp)) (ptr .r1 aE) (4 * g.e),
        .block (scr G.pLen .r0 sA ++ ([.movw .r1 (BitVec.ofNat 16 (wa G.pLen / 8))] : List Instr)),
        .call g.powName g.powCode,
        copyN (ptr .r0 aG) (scr G.pLen .r1 (sA + g.powRes)) G.pLen,
        VG.Impl.Rsa.Arm.Keys.seqs (ltS slG aOne aG),
        .block [.ldr .r1 .r8 slG, .cmp .r1 (.imm 0)],
        .ite .eq (.block [])
          (VG.Impl.Rsa.Arm.Keys.seqs [storeBE G.pLen aG sG G.pLen, .block (stImm fG 1)])])
      (St G (if 1 < hv ^ ev % pv then
        ({ c0 with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c0.cl }).setV fG 1 else c0) X) := by
  obtain ⟨cm, cb, ce, cr, cs⟩ := certs
  rw [hp] at cm cb ce cr cs
  rw [hpm] at cm; rw [hpb] at cb; rw [hpe] at ce; rw [hpr] at cr
  rw [hpm, hpb, hpe, hpr]
  have w4 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  have hpL : 0 < G.pLen := by omega_arith
  have sz : ∀ i, i ≤ 11 → sA + VG.Impl.Mont.Arm.Dynamic.slot n i + G.pLen ≤ sK G.pLen := fun i hi => by
    have := Nat.mul_le_mul_right (8 * n + 8) (show i + 1 ≤ 12 by omega_arith)
    simp only [Nat.add_mul, Nat.one_mul] at this
    simp only [contextBytes, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride, sK, wa] at hctx ⊢; omega_arith
  have hsK : sA ≤ sK G.pLen := by simp only [sK]; omega_arith
  have ap : ∀ o k, sA ≤ o → ∀ x ∈ c.cl, x ∈ c.cl ∧ Apart o k x := fun o k ho x hx =>
    ⟨hx, .inl (by have := hcl x hx; simp only [sG, sA] at *; omega_arith)⟩
  generalize hr : hv ^ ev % pv = r
  have rlt : r < pv := hr ▸ Nat.mod_lt _ (by omega_arith)
  -- The modulus, the base and the exponent.
  refine VP.seq ((copyOut_vp (E := fun _ => True) cm rfl hP hpL (by omega_arith) (by simpa [modS] using sz 0 (by omega_arith))
    (ap _ _ (by simp only [modS, VG.Impl.Mont.Arm.Dynamic.slot]; omega_arith)) fun _ _ _ _ => trivial).mono (fun σ s h => ⟨h, trivial⟩) fun σ t h => h)
    ?_
  refine VP.seq ((copyOut_vp (E := fun m => Fit G → (m.read (G.sa (sA + modS n)) (8 * n)).toNat = pv) cb rfl hHm hpL
    (by omega_arith) (by simpa [baseS] using sz 8 (by omega_arith)) (ap _ _ (by simp only [baseS, VG.Impl.Mont.Arm.Dynamic.slot]; omega_arith))
    fun m m' e f fit => by
      rw [scr_keep fit f (by simp only [modS, baseS, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride]; omega_arith) (by simpa [baseS] using sz 8 (by omega_arith))
        (by rw [hn]; simpa [modS] using sz 0 (by omega_arith))]; exact e fit).mono
    (fun σ s ⟨h, _, e⟩ => ⟨h, fun _ => by rw [hn, e, hPv, Nat.mod_eq_of_lt hplt]⟩) fun σ t h => h) ?_
  refine VP.seq ((copyOut_vp (E := fun m => Fit G → (m.read (G.sa (sA + modS n)) (8 * n)).toNat = pv ∧
      (m.read (G.sa (sA + baseS n)) (8 * n)).toNat = hv) ce rfl hE (by omega_arith)
    (by omega_arith) (by have := sz 11 (by omega_arith); simp only [expS] at *; omega_arith) (ap _ _ (by simp only [expS, VG.Impl.Mont.Arm.Dynamic.slot]; omega_arith))
    fun m m' e f fit => by
      rw [scr_keep fit f (by simp only [modS, expS, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride]; omega_arith)
          (by have := sz 11 (by omega_arith); simp only [expS] at *; omega_arith) (by rw [hn]; simpa [modS] using sz 0 (by omega_arith)),
        scr_keep fit f (by simp only [baseS, expS, VG.Impl.Mont.Arm.Dynamic.slot, VG.Impl.Mont.Arm.Dynamic.stride]; omega_arith)
          (by have := sz 11 (by omega_arith); simp only [expS] at *; omega_arith) (by rw [hn]; simpa [baseS] using sz 8 (by omega_arith))]
      exact e fit).mono
    (fun σ s ⟨h, e1, e⟩ => ⟨h, fun fit => ⟨e1 fit, by rw [hn, e, hHv, Nat.mod_eq_of_lt hvlt]⟩⟩) fun σ t h => h) ?_
  -- The exponentiation.
  refine VP.assoc (VP.seq ((powCall_vp (X := X) (hv := hv) (cl' := c.cl) ok rfl hctx hpodd hp1
    (fun x hx => ap _ _ (Nat.le_refl _) x hx)).mono (fun σ s ⟨h, e1, e⟩ =>
      ⟨h, (e1 h.1.fit).1, (e1 h.1.fit).2, by
        rw [e, hEv, Nat.mod_eq_of_lt (by rwa [show 8 * (4 * g.e) = 32 * g.e by omega_arith])]⟩) fun σ t h => h) ?_)
  -- g into its array.
  refine VP.seq ((copyIn_vp (v := r) cr rfl (by decide) (by omega_arith) (by simpa [resS] using sz 9 (by omega_arith))).mono
    (fun σ s ⟨h, e⟩ => ⟨h, by rw [← hn, e, hr]⟩) fun σ t h => h) ?_
  -- 1 < g.
  have b2le : ∀ b : Bool, b2n b ≤ 1 := fun b => by cases b <;> decide
  have vG : KU c.A aG r aG = r := by kv_simp
  have vO' : KU c.A aG r aOne = 1 := by kv_simp; exact hOv
  refine VP.seq (ltS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.Keys.sub3 aTmp aOne aG), rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) (.block [.str .r11 .r8 slG]), rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩)
    (by decide)) ?_
  refine VP.seq (slotCmp_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (.block [.ldr .r1 .r8 slG, .cmp .r1 (.imm 0)]), rfl⟩ (by simp)
      (by kv_simp; exact b2le _)) ?_
  have kG : ∀ j ∈ c0.live, j ∈ aG :: c.live ∧ KU c.A aG r j = c0.A j := fun j hj => by
    have : j ≠ aG := fun e => hGl (e ▸ hj)
    refine ⟨List.mem_cons_of_mem _ (eA j hj).1, ?_⟩
    simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, this, ite_false]; exact (eA j hj).2
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- g ≤ 1: nothing stored.
    refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, e⟩, z⟩ => ⟨?_, x⟩
    rw [e] at z
    have nr : ¬1 < r := by
      intro h1; simp only [Option.some.injEq, decide_eq_true_eq] at z
      kv_simp at z hOv; simp [hOv, b2n, h1] at z
    simp only [nr, ↓reduceIte]
    exact h.mono (fun o ho => ⟨eLS ▸ ho, by rw [eV]⟩) (fun y hy => ecl ▸ hy) kG
      (fun d hd => by rw [ek] at hd; simp at hd)
  · -- g > 1: stored, and fG := 1.
    by_cases hr1 : 1 < r
    swap
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not] at z
      kv_simp at z hOv; simp [hOv, b2n, hr1] at z
    refine VP.seq ((storeBE_vp (cl' := c.cl) cs rfl (by simp) hpL (by omega_arith)
      (by simp only [sG, sK, sA, wa]; omega_arith) fun x hx => ⟨by exact hx, .inl (hcl x hx)⟩).mono
      (fun σ s h => h.1.1) fun σ t h => h) ?_
    simp only [hr1, ↓reduceIte]
    refine stImm_vp (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨?_, h.2⟩
    refine h'.mono (fun o ho => ?_) (fun y hy => ?_) (fun j hj => kG j hj) (fun d hd => by rw [ek] at hd; simp at hd)
    · simp only [List.mem_cons] at ho ⊢
      refine ⟨ho.imp id (eLS ▸ ·), ?_⟩
      simp only [upd]; split
      · rfl
      · rw [eV]
    · simp only [List.mem_cons] at hy ⊢
      rcases hy with rfl | hy
      · left; rw [vG, Nat.mod_eq_of_lt (by omega_arith)]
      · right; exact ecl ▸ hy

theorem gStep_vp {g : Geo} {n : Nat} (certs : GStepCerts g) (ok : PowOk n g.e g.powCode) (hp : g.pLen = G.pLen)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hn : 8 * n = G.pLen)
    (hpm : g.powMod = modS n) (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa G.pLen) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    {pv ev i : Nat} (hP : aP ∈ c.live) (hPv : c.A aP = pv) (hE : aE ∈ c.live) (hEv : c.A aE = ev)
    (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1) (hO : aOne ∈ c.live) (hOv : c.A aOne = 1)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hGl : aG ∉ c.live) (hkls : c.kls = [])
    (hpodd : pv % 2 = 1) (hp1 : 1 < pv) (hplt : pv < 2 ^ (8 * G.pLen)) (hev : ev < 2 ^ (32 * g.e))
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sG)
    (hH : fH ∈ c.LS) (hHv : c.V fH = G.hs + BitVec.ofNat 32 i) (hi : i + G.pLen ≤ G.hsLen)
    (hhsb : G.hsB.length = G.hsLen) :
    VP (St G c X) g.gStep (St G (gOut c G (Spec.Dsa.decodeBE (hAt G i)) pv ev) X) := by
  have w4 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  have hsG : sG = 1728 := rfl
  have hAv : sA = 4096 := rfl
  have hpL : 0 < G.pLen := by omega_arith
  generalize hhv : Spec.Dsa.decodeBE (hAt G i) = hv
  have hal : (hAt G i).length = G.pLen := by
    simp only [hAt, List.length_take, List.length_drop, hhsb]; omega_arith
  have hvlt : hv < 2 ^ (8 * G.pLen) := by
    rw [← hhv]; have := VG.Proof.Dsa.decodeBE_lt (hAt G i)
    rwa [hal, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  -- Back to `c`: its arrays kept, nothing else.
  have back : ∀ (c' : Cfg) σ s, SS G σ c' s → c'.V = c.V → c'.LS = c.LS → c'.cl = c.cl →
      (∀ j ∈ c.live, j ∈ c'.live ∧ c'.A j = c.A j) → SS G σ c s := fun c' σ s h e1 e2 e3 e4 =>
    h.mono (fun o ho => ⟨e2 ▸ ho, by rw [e1]⟩) (fun y hy => e3 ▸ hy) e4 (fun d hd => by rw [hkls] at hd; simp at hd)
  unfold Geo.gStep
  rw [hp]
  -- h.
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r4 = G.hs + BitVec.ofNat 32 i)
    (ld_vp (c := fun _ => c) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hH).trans hHv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r4]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r4 = G.hs + BitVec.ofNat 32 i) ∧
      s.gpr .r6 = BitVec.ofNat 32 G.pLen)
    (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block [.movw .r6 (BitVec.ofNat 16 1)]),
      rfl⟩ (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨⟨h, x⟩, r4⟩ => wp_movw fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r6]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r4]⟩,
          by rw [u.gpr, setWidth_ofNat16 (by omega_arith)]⟩) ?_
  refine VP.seq ((loadAt_vp (c := c) (X := X) (src := G.hs + BitVec.ofNat 32 i) (bs := hAt G i)
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.CrtValues.load aH), rfl⟩ (by decide) hal hpL (by omega_arith)
    fun σ s ⟨h, _⟩ => h.gi.hSrc hi hpL).mono (fun σ s ⟨⟨h, r4⟩, r6⟩ => ⟨h, r4, r6⟩) fun _ _ h => h.1) ?_
  rw [hhv]
  -- 1 < h, h < p − 1 and both.
  refine VP.seq (ltS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.Keys.sub3 aTmp aOne aH), rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) (.block [.str .r11 .r8 slLo]), rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩)
    (by decide)) ?_
  refine VP.seq (ltS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (VG.Impl.Rsa.Arm.Keys.sub3 aTmp aH aPm1), rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) (.block [.str .r11 .r8 slHi]), rfl⟩
    (by simp) (by simp [hM]) (by decide) (by decide) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩)
    (by decide)) ?_
  have b2le : ∀ b : Bool, b2n b ≤ 1 := fun b => by cases b <;> decide
  have b2one : ∀ p : Prop, [Decidable p] → (b2n (decide p) = 1 ↔ p) := fun p _ => by
    by_cases hp' : p <;> simp [b2n, hp']
  refine VP.seq (andCmp_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
      (.block (VG.Impl.Rsa.Arm.Keys.andS slLo slLo slHi ++ [.ldr .r1 .r8 slLo, .cmp .r1 (.imm 0)])), rfl⟩
    (by decide) (by simp) (by simp) (by kv_simp; exact b2le _) (by kv_simp; exact b2le _)) ?_
  have vO : KU c.A aH hv aOne = 1 := by kv_simp; exact hOv
  have vH : KU c.A aH hv aH = hv := by kv_simp
  have vM : KU c.A aH hv aPm1 = pv - 1 := by kv_simp; exact hMv
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- Out of range: nothing more.
    refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, e⟩, z⟩ => ⟨?_, x⟩
    rw [e] at z
    have nr : ¬(1 < hv ∧ hv < pv - 1) := by
      intro hr; simp only [Option.some.injEq, decide_eq_true_eq] at z
      kv_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact z ⟨(b2one _).mpr hr.1, (b2one _).mpr hr.2⟩
    have nc : ¬(1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv) := fun hc => nr ⟨hc.1, hc.2.1⟩
    simp only [gOut, nc, ↓reduceIte]
    refine back _ σ s h rfl rfl rfl fun j hj => ⟨by simp [hj], ?_⟩
    have : j ≠ aH := fun e => hHl (e ▸ hj)
    simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, this, ite_false]
  · by_cases hr : 1 < hv ∧ hv < pv - 1
    swap
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not, not_not] at z
      kv_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact hr ⟨(b2one _).mp z.1, (b2one _).mp z.2⟩
    have eq : gOut c G hv pv ev = if 1 < hv ^ ev % pv then
        ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1 else c := by
      simp only [gOut, hr, true_and]
    rw [eq]
    have kH : ∀ j ∈ c.live, j ∈ aH :: c.live ∧ KU c.A aH hv j = c.A j := fun j hj => by
      have : j ≠ aH := fun e => hHl (e ▸ hj)
      exact ⟨List.mem_cons_of_mem _ hj, by simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, this, ite_false]⟩
    exact (gPow_vp (c := { c with A := KU c.A aH hv, live := aH :: c.live }) certs ok hp hn hpm hpb hpe hpr
      hctx he4 he0 (List.mem_cons_of_mem _ hP) ((kH _ hP).2.trans hPv) (List.mem_cons_of_mem _ hE)
      ((kH _ hE).2.trans hEv) List.mem_cons_self (by kv_simp) (List.mem_cons_of_mem _ hO) ((kH _ hO).2.trans hOv)
      (by simp only [List.mem_cons, not_or]; exact ⟨by decide, hTl⟩) hGl hpodd hp1 hplt hev hvlt hcl
      rfl rfl rfl kH hkls).mono
      (fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy)
        (fun j hj => ⟨hj, rfl⟩) (fun d hd => by simp only [hkls, List.not_mem_nil] at hd), x⟩) fun _ _ h => h

end

end VG.Proof.Dsa.Arm.Gen
