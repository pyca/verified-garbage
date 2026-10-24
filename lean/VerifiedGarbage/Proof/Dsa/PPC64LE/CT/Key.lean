module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Check
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# DSA on PPC64LE: constant time of the checks of the key after the sizes

`oddsTail_rel`: two runs of the checks after `sizes` (p and q odd,
`p mod q = 1`, g and y in the subgroup) for the same public data leak the
same trace. The taint analysis checks the code between the branches on the
checks' results (`t1`–`t8`, from the registers each phase fixes), and each
phase states the result as a fact of the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The registers `rs` hold the values `x`. -/
def FixR (rs : List Reg) (x : Reg → BitVec 64) (s : State) : Prop := ∀ r ∈ rs, s.gpr r = x r

theorem pins_fixR (rs : List Reg) : Pins (FixR rs) rs :=
  fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm

/-- Code the taint analysis checks from the registers `rs`, for any phase
that fixes them. -/
theorem rel_pins {α : Type} {Φ : α → State → Prop} {rs : List Reg} {c : Prog isa} {Q : State → State → Prop}
    (h : Pins Φ rs) (t : RelCT isa (Two (FixR rs)) c Q) : RelCT isa (Two Φ) c Q :=
  t.mono (fun s₁ _ ⟨a, h₁, h₂, hsp⟩ => ⟨s₁.gpr, fun _ _ => rfl, fun r hr => (h a _ _ h₁ h₂ r hr).symm, hsp⟩)
    fun _ _ q => q

/-- The registers of the P space's `Env`, and `r23`. -/
def envRegs' : List Reg := [.r10, .r11, .r29, .r31, .r23]

theorem t1 : RelCT isa (Two (FixR (coreRegs ++ []))) (.block (ptrP ++ odd)) fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t2 : RelCT isa (Two (FixR (coreRegs ++ []))) (.block (ptrQ ++ odd)) fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t3 : RelCT isa (Two (FixR (coreRegs ++ []))) pModQ fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t4 : RelCT isa (Two (FixR (coreRegs ++ []))) setupP fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t5 : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) (.seq (.seq (.block ptrG) (loadArr 4)) elemRange)
    fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t6 : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) elemOrder fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)
theorem t8 : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) (.seq (.seq (.block ptrY) (loadArr 4)) elemRange)
    fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)

/-! ## The key's values -/

def VD.p (v : VD) : Nat := Spec.Dsa.decodeBE v.pB
def VD.q (v : VD) : Nat := Spec.Dsa.decodeBE v.qB
/-- The number at octet `o` of the key, `p_len` octets (g or y). -/
def VD.e (v : VD) (o : Nat) : Nat := Spec.Dsa.decodeBE (v.at o v.L.pl)

/-- After the sizes, both odd. -/
def KO (v : VD) : Prop := SzOk v ∧ v.p % 2 = 1 ∧ v.q % 2 = 1
/-- And `p mod q = 1`. -/
def KM (v : VD) : Prop := KO v ∧ v.p % v.q = 1
/-- The number at octet `o` is in `(1, p)`, and in the subgroup. -/
def ERange (o : Lay → Nat) (v : VD) : Prop := 1 < v.e (o v.L) ∧ v.e (o v.L) < v.p
def EOk (o : Lay → Nat) (v : VD) : Prop := ERange o v ∧ v.e (o v.L) ^ v.q % v.p = 1

theorem KO.bounds {v : VD} (h : KO v) : 1 < v.p ∧ 255 < v.q ∧ v.q < v.p :=
  VG.Proof.Dsa.supported_bounds h.1

/-! ## The phases -/

/-- After p's oddness check. -/
def O1 : VD → State → Prop := Ph VD.qb fun v s => FixL [] s ∧ SzOk v ∧ (s.gpr .r0 = 0 ↔ v.p % 2 = 1)
/-- After q's. -/
def O2 : VD → State → Prop := Ph VD.qb fun v s =>
  FixL [] s ∧ SzOk v ∧ v.p % 2 = 1 ∧ (s.gpr .r0 = 0 ↔ v.q % 2 = 1)
/-- After `pModQ`. -/
def OM : VD → State → Prop := Ph VD.qb fun v s => FixL [] s ∧ KO v ∧ (s.gpr .r0 = 0 ↔ v.p % v.q = 1)

/-- The P space's registers. -/
def envP (v : VD) : List (Reg × BitVec 64) :=
  [(.r10, off v.L.S (slot v.L.wp 0)), (.r11, BitVec.ofNat 64 (2 * v.L.wp)),
    (.r29, BitVec.ofNat 64 (8 * (v.L.wp + 2))), (.r31, v.L.S), (.r23, v.L.S)]

/-- In the P space, with p and `R² mod p` in arrays 0 and 8. -/
def PF (v : VD) (s : State) : Prop :=
  InP s v.L ∧ arrP s.mem v.L 0 = v.p ∧ word s.mem v.L.S (slot v.L.wp 0 + 8 * v.L.wp) = 0 ∧
    arrP s.mem v.L 8 = 2 ^ (128 * v.L.wp) % v.p

/-- In the P space, the key satisfying `K`. -/
def PP (K : VD → Prop) : VD → State → Prop := Ph VD.qb fun v s => FixL (envP v) s ∧ PF v s ∧ K v
/-- After an element's range check. -/
def PE (c : VD → Prop) : VD → State → Prop := Ph VD.qb fun v s => FixL (envP v) s ∧ (s.gpr .r0 = 0 ↔ c v)
/-- After an element's check. -/
def CC (K c : VD → Prop) : VD → State → Prop := Ph VD.qb fun v s =>
  FixL (envP v) s ∧ PF v s ∧ K v ∧ (s.gpr .r0 = 0 ↔ c v)
/-- Before `rest`. -/
def K9 : VD → State → Prop := Ph VD.qb fun _ s => FixL [] s ∧ True

theorem pins_O1 : Pins O1 (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_O2 : Pins O2 (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_OM : Pins OM (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_S5' : Pins S5 (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl
theorem pins_PP (K : VD → Prop) : Pins (PP K) (coreRegs ++ envRegs') := pins_fixL _ _ fun _ => rfl
theorem pins_PE (c : VD → Prop) : Pins (PE c) (coreRegs ++ envRegs') := pins_fixL _ _ fun _ => rfl

theorem envP_of {v : VD} {s : State} (h : InP s v.L) : FixL (envP v) s := by
  simp only [FixL, envP, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨h.env.h10, h.env.h11, h.env.h29, h.env.h31, h.h23⟩

theorem body_out {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Body L m m') : Outside L.S 0 L.Z m m' :=
  h.mono (Nat.zero_le _) (by have := hL.z256; omega)

theorem ql_bounds {v : VD} {s : State} (h : Base v s) : 20 ≤ v.L.ql ∧ v.L.ql ≤ 32 := h.ok.ql

/-! ## The steps between the branches -/

theorem w_O1 {v : VD} {s : State} (h : S5 v s) : WP isa (.block (ptrP ++ odd)) s (O1 v) := by
  obtain ⟨B, r2, -, hsz⟩ := h
  have hb := pl_bounds B
  rw [WP.block_append_iff]
  refine WP.mono (ptrP_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (odd_ok a12 a6 (by omega) (by omega) fun i hi => B1.hk.rd i (by omega))
    fun u ⟨⟨b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, fixL_nil _, hsz, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [b0, m1, B.bytesP]; rfl

theorem w_O2 {v : VD} {s : State} (h : O1 v s ∧ s.gpr .r0 = 0) : WP isa (.block (ptrQ ++ odd)) s (O2 v) := by
  obtain ⟨⟨B, r2, -, hsz, e0⟩, z⟩ := h
  have hb := ql_bounds B
  rw [WP.block_append_iff]
  refine WP.mono (ptrQ_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (odd_ok a12 a6 (by omega) (by omega)
      fun i hi => (B1.hk.sub (o := v.L.pl) (k := v.L.ql) (by omega)).rd i hi)
    fun u ⟨⟨b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, fixL_nil _, hsz,
      e0.mp z, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [b0, m1, B.bytesQ]; rfl

theorem w_OM {v : VD} {s : State} (h : O2 v s ∧ s.gpr .r0 = 0) : WP isa pModQ s (OM v) := by
  obtain ⟨⟨B, r2, -, hsz, hpo, e0⟩, z⟩ := h
  have ko : KO v := ⟨hsz, hpo, e0.mp z⟩
  have bd := ko.bounds
  refine WP.mono (pModQ_ok B.ok B.scr B.regs B.hk (by rw [B.q]; exact Nat.lt_trans (by decide) bd.2.1))
    fun t ⟨⟨_, _, _, r0, qb⟩, k⟩ => ⟨B.step k (body_out B.ok (qb.body B.ok)), ?_, fixL_nil _, ko, ?_⟩
  · rw [k.gpr .r2 (by decide), r2]
  · rw [r0, B.p, B.q]; rfl

theorem w_P {v : VD} {s : State} (h : OM v s ∧ s.gpr .r0 = 0) : WP isa setupP s (PP KM v) := by
  obtain ⟨⟨B, r2, -, ko, e0⟩, z⟩ := h
  have bd := ko.bounds
  refine WP.mono (setupP_ok B.ok B.scr B.regs B.hk (by rw [B.p]; exact bd.1))
    fun t ⟨⟨ip, p0, ptop, p8, pb⟩, k⟩ => ⟨B.step k (body_out B.ok (pb.body B.ok)), ?_, envP_of ip,
      ⟨ip, ?_, ptop, ?_⟩, ko, e0.mp z⟩
  · rw [k.gpr .r2 (by decide), r2]
  · rw [p0, B.p]; rfl
  · rw [p8, B.p]; rfl

/-! ## An element's check -/

section Elem

variable (ptr : List Instr) (o : Lay → Nat) (ho : ∀ L : Lay, o L + L.pl ≤ 3 * L.pl + L.ql)
  (hptr : ∀ {s : State} {L : Lay} {key sig dig : Addr}, Regs s L key sig dig →
    WP isa (.block ptr) s fun t =>
      (t.gpr .r12 = off key (o L) ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [.r0, .r6, .r12] s t)

include ho hptr in
/-- The pointer, the load and the range check. -/
theorem w_pre {K : VD → Prop} {v : VD} {s : State} (h : PP K v s) :
    WP isa (.seq (.seq (.block ptr) (loadArr 4)) elemRange) s (PE (ERange o) v) := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, -⟩, -⟩ := h
  have hL := B.ok
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hqZ : v.L.qOff + 1600 ≤ v.L.Z := by have := hL.buf_end; simp only [Lay.bOff] at this; omega
  have hq28 : v.L.qOff = slot v.L.wp 28 := rfl
  have hov := ho v.L
  have e0 := Lay.slot_eq v.L.wp 0; have e3 := Lay.slot_eq v.L.wp 3; have e4 := Lay.slot_eq v.L.wp 4
  have e8 := Lay.slot_eq v.L.wp 8; have e28 := Lay.slot_eq v.L.wp 28
  refine WP.seq (WP.seq (WP.mono (hptr B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_))
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  have en1 := ip.env.keep k1 (by decide)
  have he := B1.hk.sub (o := o v.L) (k := v.L.pl) hov
  refine WP.mono (loadArr_ok en1 (j := 4) (by decide) a12 a6 (by omega) (by omega) he.rd
    (fun i hi x hx => he.sep i hi x (by omega))) fun u ⟨⟨v4, top4, o2, a10⟩, k2⟩ => ?_
  have en2 := env_keep10 en1 k2 (by decide) a10
  have B2 := B1.step k2 (o2.mono (Nat.zero_le _) (by omega))
  refine WP.mono (elemRange_ok en2 top4) fun w ⟨⟨r0, _, o3, en3⟩, k3⟩ => ?_
  have B3 := B2.step k3 (o3.mono (Nat.zero_le _) (by omega))
  have p1 : arr u.mem v.L.S v.L.wp 0 = v.p := by
    rw [arr, Outside.val32 o2 (by omega) (by omega), m1]; exact p0
  have x4 : arr u.mem v.L.S v.L.wp 4 = v.e (o v.L) := by
    rw [arr, v4, m1, B.bytes hov]; rfl
  refine ⟨B3, ?_, ?_, ?_⟩
  · rw [k3.gpr .r2 (by decide), k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, envP, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨en3.h10, en3.h11, en3.h29, en3.h31,
      (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans ((k1.gpr .r23 (by decide)).trans ip.h23))⟩
  · rw [r0, x4, p1]; rfl

include ho hptr in
/-- The pointer and `checkElem`. -/
theorem w_elem {K : VD → Prop} (hK : ∀ v, K v → 2 ≤ v.p ∧ v.p % 2 = 1) {v : VD} {s : State}
    (h : PP K v s) : WP isa (.seq (.block ptr) checkElem) s (CC K (EOk o) v) := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, p8⟩, kv⟩ := h
  have hL := B.ok
  have hov := ho v.L
  obtain ⟨hp, hpo⟩ := hK v kv
  refine WP.seq (WP.mono (hptr B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (checkElem_ok hL B1.regs (ip.keep k1 (by decide)) B1.hk (B1.hk.sub (o := o v.L) (k := v.L.pl) hov)
      a12 a6 (by rw [m1]; exact p0) (by rw [m1]; exact ptop) hp hpo (by rw [m1]; exact p8))
    fun u ⟨⟨ip', p0', ptop', p8', r0, pb⟩, k2⟩ =>
      ⟨B1.step k2 (body_out hL (pb.body hL)), ?_, envP_of ip', ⟨ip', p0', ptop', ?_⟩, kv, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [p8', m1]; exact p8
  · rw [r0, B1.bytes hov, B1.q, EOk, ERange, and_assoc]; rfl

include ho hptr in
theorem elem_rel
    (hT : RelCT isa (Two (FixR (coreRegs ++ envRegs'))) (.seq (.seq (.block ptr) (loadArr 4)) elemRange)
      fun _ _ => True)
    {K : VD → Prop} (hK : ∀ v, K v → 2 ≤ v.p ∧ v.p % 2 = 1) :
    RelCT isa (Two (PP K)) (.seq (.block ptr) checkElem) (Two (CC K (EOk o))) := by
  refine two_post ?_ fun _ _ h => w_elem ptr o ho hptr hK h
  unfold checkElem andThen
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (rel_pins (pins_PP K) hT) fun _ _ h => w_pre ptr o ho hptr h)
    (rel_ite_zero (zero_iff_agree (ERange o) fun _ _ h => h.2.2.2) (rel_weaken (rel_pins (pins_PE _) t6))
      (rel_weaken (RelCT.block_nil fun _ _ _ => trivial)))))

end Elem

/-! ## The checks after the sizes -/

theorem KM_p {v : VD} (h : KM v) : 2 ≤ v.p ∧ v.p % 2 = 1 := ⟨h.1.bounds.1, h.1.2.1⟩

theorem oddsTail_rel {rest fail : Prog isa} {Q : State → State → Prop}
    (hrest : RelCT isa (Two K9) rest Q)
    (hfail : ∀ Φ : VD → State → Prop, (∀ v s, Φ v s → Base v s) → RelCT isa (Two Φ) fail Q) :
    RelCT isa (Two S5) (odds (andThen pModQ (.seq setupP (andThen (.seq (.block ptrG) checkElem)
      (andThen (.seq (.block ptrY) checkElem) rest fail) fail)) fail) fail) Q := by
  have fl : ∀ {Φ E : VD → State → Prop}, (∀ v s, Φ v s → Base v s) →
      RelCT isa (Two fun v s => Φ v s ∧ E v s) fail Q := fun h => hfail _ fun v s h' => h v s h'.1
  have hG := elem_rel ptrG (fun L => L.pl + L.ql) (fun L => by omega) (fun h => ptrG_ok h) t5 (K := KM)
    fun _ => KM_p
  have hY := elem_rel ptrY (fun L => 2 * L.pl + L.ql) (fun L => by omega) (fun h => ptrY_ok h) t8
    (K := fun v => KM v ∧ EOk (fun L => L.pl + L.ql) v) fun _ h => KM_p h.1
  unfold odds andThen
  refine RelCT.seq (two_post (rel_pins pins_S5' t1) fun _ _ h => w_O1 h)
    (rel_ite_zero (zero_iff_agree _ fun _ _ h => h.2.2.2.2) ?_ (fl fun _ _ h => h.1))
  refine RelCT.seq (two_post (rel_pins (pins_and pins_O1) t2) fun _ _ h => w_O2 h)
    (rel_ite_zero (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (fl fun _ _ h => h.1))
  refine RelCT.seq (two_post (rel_pins (pins_and pins_O2) t3) fun _ _ h => w_OM h)
    (rel_ite_zero (zero_iff_agree _ fun _ _ h => h.2.2.2.2) ?_ (fl fun _ _ h => h.1))
  refine RelCT.seq (two_post (rel_pins (pins_and pins_OM) t4) fun _ _ h => w_P h) (RelCT.seq
    hG (rel_ite_zero (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (fl fun _ _ h => h.1)))
  refine RelCT.seq (hY.mono
    (fun _ _ => two_mono fun _ _ ⟨⟨B, r2, fx, pf, k, e⟩, z⟩ => ⟨B, r2, fx, pf, k, e.mp z⟩) fun _ _ h => h)
    (rel_ite_zero (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (fl fun _ _ h => h.1))
  exact hrest.mono (fun _ _ => two_mono fun _ _ ⟨⟨B, r2, _⟩, _⟩ => ⟨B, r2, fixL_nil _, trivial⟩) fun _ _ h => h

end VG.Proof.Dsa.PPC64LE
