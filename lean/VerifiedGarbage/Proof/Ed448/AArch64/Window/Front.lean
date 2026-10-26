module

import VerifiedGarbage.Proof.Ed448.AArch64.VerifyStages
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
public import VerifiedGarbage.Proof.X448.AArch64.Base.Digit
public import VerifiedGarbage.Proof.X448.AArch64.Fast.SaveX
public import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
public import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.X448.AArch64.Ladder
import VerifiedGarbage.Proof.Ed448.AArch64.DecodeOps
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBytes
public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyEntry
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Impl.Curve448.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Spec.Ed448.Contract
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Formulas
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Env
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
public import VerifiedGarbage.Proof.Ed448.AArch64.DecodeSteps
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Ed448.Ref
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.X448.AArch64.Setup
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Code

/-!
# Ed448 verification on AArch64: the entry and the decodings

Untrusted: everything here is checked by Lean. `wfront`: the entry
(`ventry_ok`), the challenge copied to `KB` and the callee-saved registers
saved, the bits of `S` at `BITS`, the check of `S`, and the decodings of `A`
(negated, slots 6–7) and `R` (slots 8–9), each check ORed into `x20`
(`wfront_ok`, `FrontOut`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
open VG.Impl.X448.AArch64.Fast (saved SAVE VSAVE)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs Saved)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Proof.X448.AArch64.Fast (SavedX SavedV save_ok vsave_ok)
open VG.Proof.X448.AArch64.Base (Bits)
open VG.Proof.Ed448.AArch64 (DFrame ventry_ok sCheck_ok decodes_ok bitsAt_ok far_bytes)
open VG.Spec.Ed448 (bytesAt decodeLE decodePoint Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## What frames keep -/

theorem Saved.dframe {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : DFrame base m m') (hs : Saved base g m) :
    Saved base g m' :=
  ⟨(h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.1,
    (h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.2⟩

theorem LrSaved.dframe {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : DFrame base m m')
    (hs : LrSaved base g m) : LrSaved base g m' :=
  (h.word (Or.inr (by simp only [LRS]; omega_arith)) (Or.inl (by simp only [ACC, LRS]; omega_arith))
    (Or.inl (by simp only [CAN, LRS]; omega_arith)) (by simp only [LRS]; omega_arith)).trans hs

theorem SavedX.dframe {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : DFrame base m m') (hs : SavedX base g m) :
    SavedX base g m' := fun k hk =>
  (h.word (Or.inr (by simp only [SAVE]; omega_arith)) (Or.inl (by simp only [ACC, SAVE]; omega_arith))
    (Or.inl (by simp only [CAN, SAVE]; omega_arith)) (by simp only [SAVE]; omega_arith)).trans (hs k hk)

theorem SavedV.dframe {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : DFrame base m m') (hs : SavedV base v m) :
    SavedV base v m' := by
  have hV : VSAVE = 4736 := rfl
  refine hs.frame fun d h1 h2 => ?_
  have ho : ofs base (off base d) = d := ofs_off0' base (by omega_arith)
  exact h _ (by rw [ho]; omega_arith) (by rw [ho]; simp only [ACC]; omega_arith) (by rw [ho]; simp only [CAN]; omega_arith)

/-- The challenge's copy at `KB`. -/
def KBytes (base : Addr) (m : Mem) (b : Nat → BitVec 8) : Prop := ∀ i < 57, m (off base (KB + i)) = b i

theorem KBytes.of_frame {base : Addr} {m m' : Mem} {b : Nat → BitVec 8} (h : KBytes base m b)
    (hf : ∀ i < 57, m' (off base (KB + i)) = m (off base (KB + i))) : KBytes base m' b := fun i hi => by
  rw [hf i hi]; exact h i hi

theorem kb_ofs (base : Addr) {i : Nat} (hi : i < 57) : ofs base (off base (KB + i)) = KB + i :=
  ofs_off0' base (by simp only [KB]; omega_arith)

theorem bits_ofs (base : Addr) {t : Nat} (ht : t < 456) : ofs base (off base (BITS + t)) = BITS + t :=
  ofs_off0' base (by simp only [BITS]; omega_arith)

theorem Bits.dframe {base : Addr} {k : Nat} {m m' : Mem} (h : DFrame base m m') (hb : Bits 57 base k m) :
    Bits 57 base k m' := fun t ht => by
  rw [h _ (by rw [bits_ofs base (by omega_arith)]; simp only [BITS]; omega_arith)
    (by rw [bits_ofs base (by omega_arith)]; simp only [BITS, ACC]; omega_arith)
    (by rw [bits_ofs base (by omega_arith)]; simp only [BITS, CAN]; omega_arith)]
  exact hb t ht

/-! ## The front -/

/-- What `wfront` leaves, from the entry state `s`. -/
structure FrontOut (s : State) (base : Addr) (t : State) : Prop where
  scr : Scr t base
  bnd : VG.Proof.X448.AArch64.Fast.BEnv t.mem base
  chk : ∃ c0 cA cR : BitVec 64, t.gpr .x20 = 0 ||| c0 ||| cA ||| cR ∧
    (c0 = 0 ↔ decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57) < Spec.Ed448.L) ∧
    (cA = 0 ↔ (decodePoint (bytesAt s.mem (s.gpr .x0) 57)).isSome) ∧
    (cR = 0 ↔ (decodePoint (bytesAt s.mem (s.gpr .x1) 57)).isSome)
  na : ∀ a, decodePoint (bytesAt s.mem (s.gpr .x0) 57) = some a → slotPt t.mem base = VG.Proof.Ed448.negPoint a
  rr : ∀ r, decodePoint (bytesAt s.mem (s.gpr .x1) 57) = some r → EV t.mem base 8 = r.X ∧ EV t.mem base 9 = r.Y ∧
    r.Z = 1
  bits : Bits 57 base (decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57)) t.mem
  kb : KBytes base t.mem fun i => s.mem (s.gpr .x2 + BitVec.ofNat 64 i)
  saved : Saved base s.gpr t.mem
  savedX : SavedX base s.gpr t.mem
  savedV : SavedV base s.v t.mem
  lrs : LrSaved base s.gpr t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 0 8192 s.mem t.mem

theorem wsave_eq : wsave = (((List.range 57).flatMap fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) ++
    Impl.X448.AArch64.Fast.save) ++ Impl.X448.AArch64.Fast.vsave := by
  simp only [wsave, List.append_assoc]

/-- What the entry block leaves. -/
structure EntryOut (s : State) (base : Addr) (t : State) : Prop where
  scr : Scr t base
  bnd : BoundedEnv t.mem base
  saved : Saved base s.gpr t.mem
  savedX : SavedX base s.gpr t.mem
  lrs : LrSaved base s.gpr t.mem
  x20 : t.gpr .x20 = 0
  kb : KBytes base t.mem fun i => s.mem (s.gpr .x2 + BitVec.ofNat 64 i)
  regs : Keeps [.x12, .x20, .x4] s t
  mem : Outside base 0 8192 s.mem t.mem
  e0 : E t.mem base 0 = 0
  pB : VG.Proof.Ed448.pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E t.mem base 11 = Spec.Ed448.d

/-- After the entry (`ventry_ok`), the challenge's copy and the save of `x21`–`x28`. -/
theorem prefix_ok {s s1 : State} {base : Addr}
    (V : Scr s1 base ∧ BoundedEnv s1.mem base ∧ Saved base s.gpr s1.mem ∧ LrSaved base s.gpr s1.mem ∧
      s1.gpr .x20 = 0 ∧ Keeps [.x12, .x20, .x4] s s1 ∧ Outside base 0 8192 s.mem s1.mem ∧
      E s1.mem base 0 = 0 ∧ VG.Proof.Ed448.pt (E s1.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E s1.mem base 11 = Spec.Ed448.d)
    (rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1)
    (fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i)) :
    WP isa (.block (((List.range 57).flatMap fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) ++
      Impl.X448.AArch64.Fast.save)) s1 (EntryOut s base) := by
  obtain ⟨hs1, b1, sv1, lr1, x20₁, k1, o1, z1, pB1, d1⟩ := V
  rw [WP.block_append_iff]
  refine WP.mono (copyK_ok hs1 (k1.1 _ (by decide)) (fun i hi => by rw [k1.2.1, k1.2.2]; exact rch i hi) fch)
    fun s2 ⟨kb2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (save_ok hs2) fun t ⟨svx, o3, g3, rd3, wr3⟩ => ?_
  have o13 : Outside base SAVE 128 s1.mem t.mem :=
    (o2.mono (by simp only [SAVE, KB]; omega_arith) (by simp only [SAVE, KB]; omega_arith)).trans
      (o3.mono (Nat.le_refl _) (by omega_arith))
  have keepSlot : ∀ i : Fin 22, E t.mem base i = E s1.mem base i := fun i =>
    VG.Proof.X448.AArch64.Weak.E_outside o13 i (Or.inl (by have := i.isLt; simp only [slot, SAVE]; omega_arith))
  refine ⟨hs2.of_keeps (rs := []) ⟨fun r _ => congrFun g3 r, rd3, wr3⟩ (by decide), fun i j hj => ?_, ?_, ?_,
    lr1.outside o13 (Or.inr (by decide)), ?_, fun i hi => ?_, ?_, ?_, by rw [keepSlot]; exact z1, ?_,
    by rw [keepSlot]; exact d1⟩
  · rw [o13.limbs (Or.inl (by have := i.isLt; simp only [slot, SAVE]; omega_arith)) (by have := i.isLt; simp only [slot]; omega_arith)
      (by omega_arith)]
    exact b1 i j hj
  · exact (sv1.outside o13 (by decide))
  · intro k hk
    rw [svx k hk, congrFun (show s2.gpr = s2.gpr from rfl) _, k2.1 _ (by
      have : saved k ≠ .x4 := by revert k; decide
      simpa using this), k1.1 _ (by
      have : saved k ∉ [Reg.x12, .x20, .x4] := by revert k; decide
      exact this)]
  · rw [congrFun g3 .x20, k2.1 _ (by decide)]; exact x20₁
  · rw [o3 _ (Or.inr (by rw [kb_ofs base hi]; simp only [SAVE, KB]; omega_arith))]
    rw [kb2 i hi, o1 _ (Or.inr (fch i hi))]
  · exact (k1.trans (k2.mono (by decide))).trans ⟨fun r _ => congrFun g3 r, rd3, wr3⟩ |>.mono (by decide)
  · exact o1.trans ((o13.mono (by decide) (by decide)) : Outside base 0 8192 s1.mem t.mem) |>.trans (Outside.refl _ _ _ _)
  · simp only [VG.Proof.Ed448.pt]; rw [keepSlot 8, keepSlot 9, keepSlot 10]; exact pB1

theorem V_preserved : ∀ k < 8, VG.Impl.Curve448.AArch64.Neon.V (8 + k) ∈ preservedV := by decide

/-- The entry block: `EntryOut`, and `v8`–`v15` saved. -/
theorem entry_ok {s : State} {base : Addr} (hb3 : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1)
    (fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i)) :
    WP isa (.seq ventry (.block wsave)) s fun t => EntryOut s base t ∧ SavedV base s.v t.mem := by
  refine WP.seq (WP.mono (WP.preservedV (ventry_ok hb3 hw hn) (by lit_decide)) fun s1 ⟨V1, v1⟩ => ?_)
  rw [wsave_eq]
  refine WP.block_append_iff.mpr (WP.mono (WP.preservedV (prefix_ok V1 rch fch) (by lit_decide))
    fun s3 ⟨E3, v3⟩ => WP.mono (vsave_ok E3.scr) fun s4 ⟨svv, o4, g4, rd4, wr4⟩ => ?_)
  have hV : VSAVE = 4736 := rfl
  have k4 : Keeps [] s3 s4 := ⟨fun r _ => congrFun g4 r, rd4, wr4⟩
  refine ⟨⟨E3.scr.of_keeps k4 (by decide), fun i j hj => ?_, E3.saved.outside o4 (by decide),
    E3.savedX.outside o4 (Or.inr (by decide)), E3.lrs.outside o4 (Or.inl (by decide)),
    by rw [congrFun g4]; exact E3.x20,
    E3.kb.of_frame fun i hi => o4 _ (Or.inl (by rw [kb_ofs base hi]; simp only [KB]; omega_arith)),
    E3.regs.trans (k4.mono (by decide)), E3.mem.trans (o4.mono (by decide) (by decide)), ?_, ?_, ?_⟩,
    fun k hk => by rw [svv k hk, v3 _ (V_preserved k hk), v1 _ (V_preserved k hk)]⟩
  · rw [o4.limbs (Or.inl (by have := i.isLt; simp only [slot]; omega_arith)) (by have := i.isLt; simp only [slot]; omega_arith)
      (by omega_arith)]
    exact E3.bnd i j hj
  · rw [VG.Proof.X448.AArch64.Weak.E_outside o4 0 (Or.inl (by simp only [slot]; omega_arith))]; exact E3.e0
  · simp only [VG.Proof.Ed448.pt]
    rw [VG.Proof.X448.AArch64.Weak.E_outside o4 8 (Or.inl (by simp only [slot]; omega_arith)),
      VG.Proof.X448.AArch64.Weak.E_outside o4 9 (Or.inl (by simp only [slot]; omega_arith)),
      VG.Proof.X448.AArch64.Weak.E_outside o4 10 (Or.inl (by simp only [slot]; omega_arith))]
    exact E3.pB
  · rw [VG.Proof.X448.AArch64.Weak.E_outside o4 11 (Or.inl (by simp only [slot]; omega_arith))]; exact E3.d

theorem wfront_ok (hR : VG.Proof.Ed448.RecoverOk) {s : State} {base : Addr} (hb3 : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64)
    (rpk : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) 1)
    (rsg : ∀ i < 114, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1)
    (rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1)
    (fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 i))
    (fsg : ∀ i < 114, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 i))
    (fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i)) :
    WP isa wfront s (FrontOut s base) := by
  unfold wfront
  refine WP.seq (WP.mono (entry_ok hb3 hw hn rch fch) fun s4 ⟨E4, sv4⟩ => ?_)
  have hs4 := E4.scr
  have rr4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [E4.regs.2.1, E4.regs.2.2]
  have x1₄ : s4.gpr .x1 = s.gpr .x1 := E4.regs.1 _ (by decide)
  have x0₄ : s4.gpr .x0 = s.gpr .x0 := E4.regs.1 _ (by decide)
  -- The bits of `S`.
  refine WP.seq (WP.mono (bitsAt_ok (so := 57) (d1 := 0) (d2 := BITS) hs4 x1₄ (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun q hq => by rw [rr4]; exact rsg _ (by omega_arith))
    (fun q hq => fsg _ (by omega_arith))) fun s5 ⟨g5, rd5, wr5, o5, bits5⟩ => ?_)
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.x3, (g5 _ (by decide)).trans hs4.mask, wr5 ▸ hs4.wr, hn⟩
  have rr5 : s5.rd ++ s5.wr = s.rd ++ s.wr := by rw [rd5, wr5, rr4]
  have O5 : Outside base 0 8192 s.mem s5.mem := E4.mem.trans (o5.mono (by decide) (by decide))
  -- The check of `S`.
  refine WP.seq (WP.mono (sCheck_ok (p := s.gpr .x1) ((g5 _ (by decide)).trans x1₄)
    (fun j hj => by rw [rr5]; exact rsg _ (by omega_arith))) fun s6 ⟨⟨c0, hc0, x6'⟩, m6, k6⟩ => ?_)
  rw [far_bytes O5 (fun i hi => by rw [Offset.add_add]; exact fsg _ (by omega_arith))] at hc0
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  have rr6 : s6.rd ++ s6.wr = s.rd ++ s.wr := by rw [k6.2.1, k6.2.2, rr5]
  have O6 : Outside base 0 8192 s.mem s6.mem := by rw [m6]; exact O5
  have b6 : VG.Proof.X448.AArch64.Fast.BEnv s6.mem base := VG.Proof.Ed448.AArch64.benv_of_weak fun i j hj => by
    rw [m6, o5.limbs (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_arith)) (by have := i.isLt; simp only [slot]; omega_arith)
      (by omega_arith)]
    exact E4.bnd i j hj
  have e6 : ∀ i : Fin 22, E s6.mem base i = E s4.mem base i := fun i => by
    rw [m6]; exact VG.Proof.X448.AArch64.Weak.E_outside o5 i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_arith))
  -- `A` and `R`, decoded by one copy of `decode`.
  have x0₆ : s6.gpr .x0 = s.gpr .x0 := (k6.1 _ (by decide)).trans ((g5 _ (by decide)).trans x0₄)
  have x1₆ : s6.gpr .x1 = s.gpr .x1 := (k6.1 _ (by decide)).trans ((g5 _ (by decide)).trans x1₄)
  refine WP.mono (decodes_ok hR hs6 b6 (by rw [e6]; exact E4.d)
    (fun j hj => by rw [rr6, x0₆]; exact rpk _ hj) (fun j hj => by rw [x0₆]; exact fpk _ hj)
    (fun j hj => by rw [rr6, x1₆]; exact rsg _ (by omega_arith)) (fun j hj => by rw [x1₆]; exact fsg _ (by omega_arith)))
    fun t ⟨⟨cA, cR, hcA, hcR, xt⟩, nat, vt, _, hst, bt, gt, ft⟩ => ?_
  simp only [x0₆, x1₆, far_bytes O6 fpk, far_bytes O6 (fun i (hi : i < 57) => fsg _ (by omega_arith))] at hcA hcR nat vt
  have s4b : bytesAt s4.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57 = bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57 :=
    far_bytes E4.mem (fun i hi => by rw [Offset.add_add]; exact fsg _ (by omega_arith))
  have o45 : Outside base BITS 456 s4.mem s5.mem := o5
  refine ⟨hst, bt, ⟨c0, cA, cR, ?_, hc0, hcA, hcR⟩, fun a ha => nat a ha, vt, fun q hq => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xt, x6', g5 _ (by decide), E4.x20]
  · have hq' : q < 456 := hq
    rw [ft _ (by rw [bits_ofs base hq']; simp only [BITS]; omega_arith) (by rw [bits_ofs base hq']; simp only [BITS, ACC]; omega_arith)
      (by rw [bits_ofs base hq']; simp only [BITS, CAN]; omega_arith), m6]
    have := bits5 q hq'
    rw [Nat.zero_add, s4b] at this
    exact this
  · refine E4.kb.of_frame fun i hi => ?_
    have ho := kb_ofs base hi
    rw [ft _ (by rw [ho]; simp only [KB]; omega_arith) (by rw [ho]; simp only [KB, ACC]; omega_arith)
      (by rw [ho]; simp only [KB, CAN]; omega_arith), m6, o45 _ (Or.inl (by rw [ho]; simp only [KB, BITS]; omega_arith))]
  · exact Saved.dframe ft (by rw [m6]; exact E4.saved.outside o45 (by decide))
  · exact SavedX.dframe ft (by rw [m6]; exact E4.savedX.outside o45 (Or.inr (by decide)))
  · exact SavedV.dframe ft (by rw [m6]; exact sv4.outside o45 (Or.inl (by decide)))
  · exact LrSaved.dframe ft (by rw [m6]; exact E4.lrs.outside o45 (Or.inl (by decide)))
  · rw [gt.2.1, k6.2.1, rd5, E4.regs.2.1]
  · rw [gt.2.2, k6.2.2, wr5, E4.regs.2.2]
  · exact O6.trans ft.whole

end VG.Proof.Ed448.AArch64.Window
