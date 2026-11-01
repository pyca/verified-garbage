module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PrimeCall
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP

/-! # DSA parameter generation on ARMv7: a probable-prime test (`test_vp`)

`test L name code` tests the candidate at `sA` with the witnesses from
`fUsed` on: `fRes` := its status, and `fUsed` := the witnesses it read when
the tape sufficed (`testCfg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_movw wp_dp wp_subs wp_cmp op2_reg op2_imm dpVal eval_eq
  ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The stage after a test, from its result `res`. -/
def testCfg (c : Cfg) (cl : Claims) (witLen : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }.setV fRes 0
  | some (b, rest) => ({ c with cl := cl }.setV fRes (BitVec.ofNat 32 (if b then 1 else 2))).setV fUsed
      (BitVec.ofNat 32 (witLen - rest.length))

section
variable {G : GP}

/-- A stage: a state of the search with the contents `c`, and `X` of the run. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G σ c s ∧ X σ

theorem St.ss {c : Cfg} {X : State → Prop} : ∀ σ s, St G c X σ s → SS G σ c s := fun _ _ h => h.1

theorem varOk_of {o : Nat} (h : 40 ≤ o ∧ o + 4 ≤ F ∧ o % 4 = 0 ∧ o ∉ [fOut, fOutLen, fScratch, fWit, fWitLen]) :
    VarOk G o := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p hp e => h.2.2.2 ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [e]

theorem varOk_fRes : VarOk G fRes := varOk_of (by decide)
theorem varOk_fUsed : VarOk G fUsed := varOk_of (by decide)
theorem varOk_fUsedOut : VarOk G fUsedOut := varOk_of (by decide)

/-- A fixed frame word's value. -/
theorem SS.fixedV {σ s : State} {c : Cfg} (h : SS G σ c s) {o : Nat} {v : BitVec 32} (hp : (o, v) ∈ fixedWords G) :
    fw s.mem G o = v := h.gi.fixed (o, v) hp

theorem SS.slotV {σ s : State} {c : Cfg} (h : SS G σ c s) {o : Nat} (ho : o ∈ c.LS) : fw s.mem G o = c.V o :=
  h.gi.slots o ho

/-! ## The arguments -/

variable {c : Cfg} {X : State → Prop}

/-- `r0` and `r1`: the working space; `r5`: the size. -/
abbrev TR1 (G : GP) (L bits : Nat) (s : State) : Prop :=
  s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa L / 8) ∧ s.gpr .r5 = BitVec.ofNat 32 bits

theorem targs1_vp {L bits : Nat} (hL : L = G.pLen) (hb : bits < 2 ^ 16) :
    VP (St G c X) (.block (scr L .r0 sA ++
        ([.movw .r1 (BitVec.ofNat 16 (wa L / 8)), .movw .r5 (BitVec.ofNat 16 bits)] : List Instr)))
      (fun σ s => St G c X σ s ∧ TR1 G L bits s) := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sA ++ [.movw .r1 (BitVec.ofNat 16 5), .movw .r5 (BitVec.ofNat 16 5)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8])
    fun σ s ⟨h, x⟩ => ?_
  have big := h.gi.scrBig
  have hLv := h.lens
  subst hL
  refine scr_ok (d := .r0) h.r8 rfl hLv (by simp only [sK]; omega_arith) fun s₁ v₁ R₁ M₁ => wp_movw fun t₁ u₁ =>
    wp_movw fun t u => WP.block_nil ⟨⟨((h.of_rest R₁ M₁).of_rest (u₁.rest (ws := [.r1]) (by simp)) u₁.mem).of_rest
      (u.rest (ws := [.r5]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), u₁.other _ (by decide)]; exact v₁, ?_, ?_⟩
  · rw [u.other _ (by decide), u₁.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, wa]; rcases hLv with e | e | e <;> rw [e]
  · rw [u.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega_arith)]

/-- A load of a frame word whose value is known, keeping a stage. -/
theorem SS.ldK {σ s : State} (h : SS G σ c s) {o : Nat} (ho : o + 4 ≤ F + 32) (h4 : o % 4 = 0) {v : BitVec 32}
    (hv : fw s.mem G o = v) {t : Reg} (h7 : t ≠ .r7) (h8 : t ≠ .r8) (h9 : t ≠ .r9) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q :=
  h.gi.ldV ho h4 hv fun s' u => k s' (h.of_rest (u.rest (ws := [t]) (by simp)) u.mem (by simpa using h7.symm)
    (by simpa using h8.symm) (by simpa using h9.symm)) u

theorem targs2_vp {L u bits : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u) :
    VP (fun σ s => St G c X σ s ∧ TR1 G L bits s) (.block [ld .r4 fUsed, ld .r2 fWit, ld .r3 fWitLen])
      (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r4 = BitVec.ofNat 32 u ∧ s.gpr .r2 = G.wit ∧
        s.gpr .r3 = BitVec.ofNat 32 G.witLen) := by
  refine VP.ldrSp (c := [(.r4, fUsed), (.r2, fWit), (.r3, fWitLen)])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.gi.sp, h₂.1.1.gi.sp]) fun σ s ⟨⟨h, x⟩, r0, r1, r5⟩ => ?_
  refine h.ldK (o := fUsed) (by decide) (by decide) ((h.slotV hU).trans hUv) (by decide) (by decide) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fWit) (by decide) (by decide) (h₁.fixedV (v := G.wit) (by simp [fixedWords])) (by decide) (by decide)
    (by decide) fun s₂ h₂ u₂ => ?_
  refine h₂.ldK (o := fWitLen) (by decide) (by decide) (h₂.fixedV (v := BitVec.ofNat 32 G.witLen) (by simp [fixedWords])) (by decide) (by decide)
    (by decide) fun s₃ h₃ u₃ => WP.block_nil ⟨⟨h₃, x⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, u₃.gpr⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r0]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r1]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r5]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem targs3_vp {L u bits : Nat} (hu : u ≤ G.witLen) :
    VP (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r4 = BitVec.ofNat 32 u ∧ s.gpr .r2 = G.wit ∧
        s.gpr .r3 = BitVec.ofNat 32 G.witLen)
      (.block [.dp .add .r2 .r2 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .addSp .r4 fUsedOut, .cmp .r3 (.imm 0)])
      (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r2 = G.wit + BitVec.ofNat 32 u ∧
        s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧ s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut ∧
        s.z = decide (u = G.witLen)) := by
  refine VP.taint [.r2, .r3, .r4] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r2, .r3, .r4])
      (.block [.dp .add .r2 .r2 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .addSp .r4 fUsedOut, .cmp .r3 (.imm 0)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, a₁, b₁, c₁⟩ ⟨_, _, a₂, b₂, c₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [a₁, a₂]) fun σ s ⟨⟨h, x⟩, ⟨r0, r1, r5⟩, r4, r2, r3⟩ => ?_
  have wl := h.gi.witLt
  refine wp_dp (op2_reg _ _) fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ =>
    VG.Proof.Bignum.Arm.wp_stackAddr (by decide) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
  have R : Rest [.r2, .r3, .r4] s t := (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))).trans
    (f.rest _)
  have v3 : s₂.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by
    rw [u₂.gpr, dpVal, u₁.other _ (by decide), u₁.other _ (by decide), r3, r4,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith)]
  have t3 : t.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by rw [f.gpr, u₃.other _ (by decide), v3]
  refine ⟨⟨h.of_rest R (by rw [f.mem, u₃.mem, u₂.mem, u₁.mem]), x⟩, ⟨?_, ?_, ?_⟩, ?_, t3, ?_, ?_⟩
  · rw [R.gpr _ (by decide), r0]
  · rw [R.gpr _ (by decide), r1]
  · rw [R.gpr _ (by decide), r5]
  · rw [f.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, dpVal, r2, r4]
  · rw [f.gpr, u₃.gpr, u₂.sp, u₁.sp, h.gi.sp]
  · have e0 : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
    rw [z, u₃.other _ (by decide), v3, e0, ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

theorem targs4_vp {L u bits : Nat} :
    VP (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r2 = G.wit + BitVec.ofNat 32 u ∧
        s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧ s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut ∧
        s.z = decide (u = G.witLen))
      (.ite .eq (.block [ld .r2 fWit]) (.block [])) (fun σ s => St G c X σ s ∧ TArgs G L u bits s) := by
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_eq, eval_eq, h₁.2.2.2.2.2, h₂.2.2.2.2.2]) ?_ ?_
  · refine VP.ld (SS.spOk (c := fun _ => c) fun σ s h => h.1.1.1) fun σ s ⟨⟨⟨h, x⟩, ⟨r0, r1, r5⟩, r2, r3, r4, z⟩, e⟩ => ?_
    have hu : u = G.witLen := by rw [eval_eq, z] at e; simpa using e
    refine h.ldK (o := fWit) (by decide) (by decide) (h.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
      (by decide) (by decide) fun t ht ut => WP.block_nil ⟨⟨ht, x⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ut.other _ (by decide), r0]
    · rw [ut.other _ (by decide), r1]
    · rw [ut.gpr, GP.randP, ite_eq_left hu]
    · rw [ut.other _ (by decide), r3]
    · rw [ut.other _ (by decide), r4]
    · rw [ut.other _ (by decide), r5]
  · refine VP.block_nil fun σ s ⟨⟨hx, ⟨r0, r1, r5⟩, r2, r3, r4, z⟩, e⟩ => ⟨hx, r0, r1, ?_, r3, r4, r5⟩
    have hu : u ≠ G.witLen := by rw [eval_eq, z] at e; simpa using e
    rw [r2, GP.randP, ite_eq_right hu]

/-- The test's arguments. -/
theorem targs_vp {L u bits : Nat} (hL : L = G.pLen) (hb : bits < 2 ^ 16) (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 32 u) :
    VP (St G c X) (VG.Impl.Rsa.Arm.Keys.seqs [
        .block (scr L .r0 sA ++
          ([.movw .r1 (BitVec.ofNat 16 (wa L / 8)), .movw .r5 (BitVec.ofNat 16 bits)] : List Instr)),
        .block [ld .r4 fUsed, ld .r2 fWit, ld .r3 fWitLen],
        .block [.dp .add .r2 .r2 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .addSp .r4 fUsedOut, .cmp .r3 (.imm 0)],
        .ite .eq (.block [ld .r2 fWit]) (.block [])])
      (fun σ s => St G c X σ s ∧ TArgs G L u bits s) :=
  VP.seq (targs1_vp hL hb) (VP.seq (targs2_vp hU hUv) (VP.seq (targs3_vp hu) targs4_vp))

/-! ## The call -/

/-- One more known frame word. -/
theorem GI.addSlot {σ t : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS t) {o : Nat} (ho : VarOk G o)
    {v : BitVec 32} (hv : fw t.mem G o = v) : GI G σ (upd V o v) (o :: LS) t := by
  refine ⟨h.pre, h.hG, h.sp, h.rd, h.wr, h.saved, h.fixed, fun o' ho' => ?_, fun o' ho' => ?_, h.frame⟩
  · by_cases e : o' = o
    · subst e; rw [upd_self]; exact hv
    · rw [upd_ne _ _ e]; exact h.slots o' (List.mem_of_ne_of_mem e ho')
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ho
    · exact h.ls o' ho'

/-- Through the test's call: claims apart from its working space kept. -/
theorem SS.of_call {σ s t : State} {L : Nat} (h : SS G σ c s) (hL : L = G.pLen)
    (g : ∀ r ∈ [Reg.r7, .r8, .r9], t.gpr r = s.gpr r) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame [G.rs sA (wa L), G.rU, G.rBelow] s.mem t.mem) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    {cl' : Claims} (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa L) x) : SS G σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  have sA4 : sA + wa G.pLen = sK G.pLen := rfl
  have R : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] s t :=
    ⟨fun r hr => g r (by cases r <;> simp_all), rd, wr, sp⟩
  have fs : Frame [G.rScr, G.rU, G.rBelow] s.mem t.mem := f.sub fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨G.rScr, List.mem_cons_self, sw G (by omega_arith)⟩
    · exact ⟨G.rU, by simp, fun _ h => h⟩
    · exact ⟨G.rBelow, by simp, fun _ h => h⟩
  have uF : Region.Sub G.rU G.rFrame := Offset.sub_base _ (by simp only [fUsedOut, F]; omega_arith)
  have kd : ∀ r' ∈ [G.rs sA (wa G.pLen), G.rU, G.rBelow], G.rK.Disjoint r' := fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    show Region.Disjoint ⟨State.addr G.KB, _⟩ _
    rw [gi.kaddr]
    rcases hr' with rfl | rfl | rfl
    · exact gi.sdisj (.inr (by omega_arith)) big (by omega_arith)
    · exact (gi.scr_frame big).sub_right uF
    · exact gi.scr_below big
  refine ⟨gi.of_used R fs h88 h92, (g _ (by simp)).trans h.r7, (g _ (by simp)).trans h.r8, (g _ (by simp)).trans h.r9,
    fun x hx => ?_, fun x hx => h.clOk x (hcl x hx).1, fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · obtain ⟨hm, ha⟩ := hcl x hx
    have := h.clOk x hm
    rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact gi.sdisj ha (by omega_arith) (by omega_arith)
      · exact (gi.scr_frame (by omega_arith)).sub_right uF
      · exact gi.scr_below (by omega_arith)) (by omega_arith)]
    exact h.sb x hm
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- After the call: the count's word known when the tape sufficed. -/
def callCfg (c : Cfg) (cl : Claims) (witLen u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }
  | some (_, rest) => { c with cl := cl }.setV fUsedOut (BitVec.ofNat 32 (witLen - u - rest.length))

theorem primeCall_vp {L u bits : Nat} {name : String} {code : Prog isa} {cb : List Byte} {cl' : Claims}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (hu : u ≤ G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) (hcb : (sA, cb) ∈ c.cl)
    (hcbl : cb.length = bits / 8) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa L) x) :
    VP (fun σ s => St G c X σ s ∧ TArgs G L u bits s) (callWith name code)
      (fun σ t => St G (callCfg c cl' G.witLen u (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u))) X σ t ∧
        (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status
          (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u))) := by
  have bytes : ∀ σ s, SS G σ c s → Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb := fun σ s h => by
    have := h.sb _ hcb; rwa [hcbl] at this
  refine VP.of_ct (fun σ₁ σ₂ => (primeCall_ct (c := c) ok hL hu hsize hb8 hodd hbl).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ => ⟨⟨σ₁, h₁⟩, g₁, bytes _ _ h₁, ⟨σ₂, h₂⟩, g₂, bytes _ _ h₂⟩)
    fun _ _ _ => trivial) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  refine h.primeCall_ok (name := name) ok hL regs hu hsize hb8 (bytes _ _ h) hodd hbl
    fun t g sp rd wr f r0 used => ⟨⟨?_, x⟩, r0⟩
  have h' := h.of_call hL (fun r hr => g r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    sp rd wr f h88 h92 hcl
  unfold callCfg
  split
  · exact h'
  · rename_i b rest e
    refine ⟨h'.gi.addSlot varOk_fUsedOut ?_, h'.r7, h'.r8, h'.r9, h'.sb, h'.clOk, h'.arrs, h'.liveOk, h'.ksl, h'.kslOk⟩
    have := used b rest e
    show t.mem.readW _ 32 = _
    rw [Mem.readW_lo32 this]
    apply BitVec.eq_of_toNat_eq; simp

theorem status_lt (res : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status res < 3 := by
  unfold Proof.Dsa.ProbablePrime.status; split <;> decide

/-- The test's result into `fRes`, then Z iff the tape ran out. -/
theorem testRes_vp {c' : Cfg} {res : Option (Bool × Spec.RsaKeyGen.Rand)} :
    VP (fun σ t => St G c' X σ t ∧ (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status res)
      (.seq (.block (st .r0 fRes)) (.block [.cmp .r0 (.imm 0)]))
      (fun σ t => St G (c'.setV fRes (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
        isa.eval .eq t = some (decide (res = none))) := by
  have e0 : ∀ t : State, (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status res →
      t.gpr .r0 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := fun t h =>
    BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := status_lt res; omega_arith)])
  refine VP.seq (G := fun σ t => St G (c'.setV fRes (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
      t.gpr .r0 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res))
    (st_vp (c := fun _ => c') (fun σ t h => h.1.1) (by decide) varOk_fRes fun σ s t ⟨⟨_, x⟩, r0⟩ h R => ?_) ?_
  · rw [e0 s r0] at h
    exact ⟨⟨h, x⟩, by rw [R.gpr _ (by decide), e0 s r0]⟩
  refine VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (.block [.cmp .r0 (.imm 0)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨⟨h, x⟩, r0⟩ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
      ⟨⟨h.of_rest (f.rest []) f.mem, x⟩, ?_⟩
  have e00 : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
  rw [eval_eq, z, r0, e00, ofNat_beq_zero (by have := status_lt res; omega_arith)]
  congr 1
  unfold Proof.Dsa.ProbablePrime.status
  split <;> simp

/-- A piece no state reaches. -/
theorem VP.of_false {F Q : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c Q :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁ (h σ _)⟩

/-- The witnesses a test leaves are a suffix of those it is given. -/
theorem rest_le {w : Nat} {r rest : Spec.RsaKeyGen.Rand} {b : Bool} (h : Spec.Dsa.probablePrime w r = some (b, rest)) :
    rest.length ≤ r.length :=
  (VG.Proof.Dsa.Generation.probablePrime_suffix h).length_le

/-- `fUsed` := the witnesses read, unless the tape ran out. -/
theorem testTail_vp {cl' : Claims} {u cand : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u)
    (h88 : fUsedOut ∉ c.LS) (hwl : G.witB.length = G.witLen) (hu : u ≤ G.witLen) :
    VP (fun σ t => St G ((callCfg c cl' G.witLen u (Spec.Dsa.probablePrime cand (G.witB.drop u))).setV fRes
        (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.witB.drop u))))) X σ t ∧
        isa.eval .eq t = some (decide (Spec.Dsa.probablePrime cand (G.witB.drop u) = none)))
      (.ite .eq (.block []) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r1 fUsedOut, ld .r2 fUsed],
        .block [.dp .add .r2 .r2 (.reg .r1)], .block (st .r2 fUsed)]))
      (St G (testCfg c cl' G.witLen (Spec.Dsa.probablePrime cand (G.witB.drop u))) X) := by
  generalize hres : Spec.Dsa.probablePrime cand (G.witB.drop u) = res
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, e⟩, z⟩ => ?_
    rw [e] at z
    have : res = none := by simpa using z
    subst this
    exact ⟨h, x⟩
  rcases res with _ | ⟨b, rest⟩
  · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
  -- The tape sufficed: `fUsed` := `u` and the count.
  have rl := rest_le hres
  rw [List.length_drop, hwl] at rl
  let x : BitVec 32 := BitVec.ofNat 32 (G.witLen - u - rest.length)
  let st0 : BitVec 32 := BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (some (b, rest)))
  let c6 : Cfg := ({ c with cl := cl' }.setV fUsedOut x).setV fRes st0
  have v88 : c6.V fUsedOut = x := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsedOut = x; rw [upd_ne _ _ (by decide), upd_self]
  have vU : c6.V fUsed = BitVec.ofNat 32 u := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsed = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hUv]
  refine VP.seq (G := fun σ t => St G c6 X σ t ∧ t.gpr .r1 = x ∧ t.gpr .r2 = BitVec.ofNat 32 u)
    (VP.ldrSp (c := [(.r1, fUsedOut), (.r2, fUsed)]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.1.1.gi.sp, h₂.1.1.1.gi.sp]) fun σ s ⟨⟨⟨h, xx⟩, _⟩, _⟩ => ?_) ?_
  · change SS G σ c6 s at h
    refine h.ldK (o := fUsedOut) (by decide) (by decide) ((h.slotV (by simp [c6])).trans v88) (by decide)
      (by decide) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.slotV (by simp [c6, hU])).trans vU) (by decide)
      (by decide) (by decide) fun s₂ h₂ u₂ => WP.block_nil ⟨⟨h₂, xx⟩, by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  refine VP.seq (G := fun σ t => St G c6 X σ t ∧ t.gpr .r2 = BitVec.ofNat 32 (G.witLen - rest.length))
    (VP.taint [.r1, .r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1, .r2])
      (.block [.dp .add .r2 .r2 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2])
      fun σ s ⟨⟨h, xx⟩, r1, r2⟩ => wp_dp (op2_reg _ _) fun t ut => WP.block_nil
        ⟨⟨h.of_rest (ut.rest (ws := [.r2]) (by simp)) ut.mem, xx⟩, ?_⟩) ?_
  · rw [ut.gpr, dpVal, r2, r1]
    show BitVec.ofNat 32 u + BitVec.ofNat 32 (G.witLen - u - rest.length) = _
    rw [← BitVec.ofNat_add, show u + (G.witLen - u - rest.length) = G.witLen - rest.length by
      omega_using [rl, hu]]
  refine st_vp (c := fun _ => c6) (fun σ t h => h.1.1) (by decide) varOk_fUsed fun σ s t ⟨⟨_, xx⟩, r2⟩ h _ => ?_
  rw [r2] at h
  refine ⟨h.mono (fun o ho => ?_) (fun x hx => hx) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), xx⟩
  simp only [testCfg, c6, Cfg.setV, List.mem_cons] at ho ⊢
  rcases ho with rfl | rfl | ho
  · exact ⟨by simp, by simp [upd]⟩
  · refine ⟨by simp, ?_⟩
    simp only [upd, show fRes ≠ fUsed by decide, ite_false, ite_true]
    cases b <;> rfl
  · refine ⟨by simp [ho], ?_⟩
    have n88 : o ≠ fUsedOut := fun e => h88 (e ▸ ho)
    have e : st0 = BitVec.ofNat 32 (if b then 1 else 2) := by cases b <;> rfl
    simp only [upd, n88, ite_false, e]

theorem sized_lt {bits : Nat} (h : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes) : bits < 2 ^ 16 := by
  simp only [Impl.Dsa.Arm.ProbablePrime.sizes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The test of the candidate in `sA`, with the tape from `fUsed`, recording its
result in `fRes` and the witnesses it read in `fUsed`. -/
theorem test_vp {L u bits : Nat} {name : String} {code : Prog isa} {cb : List Byte} {cl' : Claims}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 32 u) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) (hcb : (sA, cb) ∈ c.cl)
    (hcbl : cb.length = bits / 8) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa L) x) :
    VP (St G c X) (test L bits name code)
      (St G (testCfg c cl' G.witLen (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u))) X) :=
  VP.seq (targs1_vp hL (sized_lt ok.sized)) (VP.seq (targs2_vp hU hUv) (VP.seq (targs3_vp hu) (VP.seq targs4_vp
    (VP.seq (primeCall_vp ok hL hu hsize hb8 hcb hcbl hodd hbl h88 h92 hcl)
      (VP.assoc (VP.seq testRes_vp (testTail_vp hU hUv h88 hwl hu)))))))

end

end VG.Proof.Dsa.Arm.Gen
