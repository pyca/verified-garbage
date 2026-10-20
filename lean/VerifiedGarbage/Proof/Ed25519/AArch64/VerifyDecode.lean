module

public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# Ed25519 verification on AArch64: `R` and `A` decoded by one loop

`decodeBoth` runs one copy of `pointDecode` twice. The count at byte `DCOUNT` is 1
for `R`, whose encoding's pointer is at byte 7944 and whose table entry is at
byte 7552, then 0 for `A` (7936 and 7424). A pass that decodes a point writes
it to its entry, counts down, and loops back if the count was 1 (`decodeStep_ok`);
a pass that does not ends the loop with 0 in `x8`. The loop ends with 1 in `x8`
and both points in their entries if both are points, else with 0
(`DecodedPair`), and its trace depends on the public encodings alone
(`decodeLoop_ct`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-! ### The blocks -/

theorem ptrAt_ok {s : State} {base : Addr} (hs : Scr s base) {c : Nat} (hc : c < 2)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 c) :
    WP isa (.block [.lsl .x .x2 .x19 3, .add .x .x2 .x2 .x0, .ldr .x .x2 .x2 7936]) s fun t =>
      t.gpr .x2 = word s.mem base (7936 + 8 * c) ∧ Keeps [.x2] s t := by
  have hshift : (BitVec.ofNat 64 c) <<< 3 = BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, show 2 ^ 3 = 8 from rfl, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega : 8 * c < 2 ^ 64)]
  have ha : BitVec.ofNat 64 (8 * c) + base + BitVec.ofNat 64 7936 = off base (7936 + 8 * c) := by
    rw [BitVec.add_comm (BitVec.ofNat 64 (8 * c)), BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
  have hin : InRegions (s.rd ++ s.wr) (off base (7936 + 8 * c)) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  have e1 : exec (.lsl .x .x2 .x19 3) s = some (s.write .x .x2 (BitVec.ofNat 64 (8 * c))) := by
    simp only [exec, read_x, show (3 : Nat) < Size.x.bits from by decide, ite_true, h19, hshift]
  have e2 : exec (.add .x .x2 .x2 .x0) (s.write .x .x2 (BitVec.ofNat 64 (8 * c))) =
      some ((s.write .x .x2 (BitVec.ofNat 64 (8 * c))).write .x .x2 (BitVec.ofNat 64 (8 * c) + base)) := by
    simp only [exec, read_x, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (by decide : ¬Reg.x0 = .x2),
      hs.x0, BitVec.setWidth_eq]
  apply WP.of_runBlock
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons,
    exec_ldr_x ⟨by decide, by decide⟩ (by
      rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.rd_write, RegUpd.rd_write, RegUpd.wr_write,
        RegUpd.wr_write, ha]
      exact hin), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self, RegUpd.mem_write, RegUpd.mem_write,
      BitVec.setWidth_eq, BitVec.setWidth_eq, ha]
  · simp only [List.mem_singleton] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]

theorem decodePtr_ok {s : State} {base : Addr} (hs : Scr s base) {c : Nat} (hc : c < 2)
    (hw : word s.mem base DCOUNT = BitVec.ofNat 64 c) :
    WP isa (.block decodePtr) s fun t => t.gpr .x19 = BitVec.ofNat 64 c ∧
      t.gpr .x2 = word s.mem base (7936 + 8 * c) ∧ Keeps [.x19, .x2] s t := by
  change WP isa (.block (([ld .x19 DCOUNT] : List Instr) ++
    ([.lsl .x .x2 .x19 3, .add .x .x2 .x2 .x0, .ldr .x .x2 .x2 7936] : List Instr))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x19 DCOUNT (by decide) (by decide)) fun a ⟨a19, ka⟩ => ?_
  refine WP.mono (ptrAt_ok (hs.of_keeps ka (by decide)) hc (a19.trans hw)) fun t ⟨t2, kt⟩ => ?_
  exact ⟨(kt.gpr _ (by decide)).trans (a19.trans hw), t2.trans (by rw [ka.mem]),
    (ka.mono (by decide)).trans (kt.mono (by decide))⟩

/-- `x9 := x19 - 1`, stored to the count, and `x8 := 1`. -/
theorem countTail_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.subImm .x .x9 .x19 1, st .x9 DCOUNT, .movz .w .x8 1 0]) s fun t =>
      t.gpr .x8 = 1 ∧ (∀ r, r ≠ .x9 → r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.mem = s.mem.writeW (off base DCOUNT) (s.gpr .x19 - 1) := by
  have e1 : exec (.subImm .x .x9 .x19 1) s = some (s.write .x .x9 (s.gpr .x19 - 1)) := by
    simp only [exec, read_x, show (1 : Nat) < 4096 from by decide, ite_true]; rfl
  apply WP.of_runBlock
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, store_sc (hs.write (by decide) _) (by decide) (by decide),
    runStep_some, runBlock_cons]
  simp only [exec, show 16 * 0 < Size.w.bits from by decide, ite_true, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r h9 h8 => ?_, rfl, rfl, rfl, ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ h8]
    exact RegUpd.gpr_write_of_ne _ _ _ h9
  · rw [RegUpd.mem_write, RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.mem_write]

/-- `x8 := 0`, `x19 := 0`. -/
theorem decodeFail_ok (s : State) :
    WP isa (.block decodeFail) s fun t => t.gpr .x8 = 0 ∧ t.gpr .x19 = 0 ∧ Keeps [.x8, .x19] s t := by
  apply WP.of_runBlock
  simp only [decodeFail, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

/-- The count set to 1. -/
theorem decodeStart_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.movz .w .x19 1 0, st .x19 DCOUNT]) s fun t =>
      word t.mem base DCOUNT = BitVec.ofNat 64 1 ∧ VerifyKeep base s t := by
  apply WP.of_runBlock
  rw [runBlock_cons]
  simp only [exec, show 16 * 0 < Size.w.bits from by decide, ite_true, runStep_some]
  have hs' (v : BitVec Size.w.bits) : Scr (s.write .w .x19 v) base :=
    ⟨(RegUpd.gpr_write_of_ne _ _ _ (by decide)).trans hs.x0, hs.wr, hs.nowrap⟩
  rw [runBlock_cons, store_sc (hs' _) (by decide) (by decide), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r h19 _ _ => RegUpd.gpr_write_of_ne _ _ _ h19, rfl, rfl, rfl, ?_⟩
  · rw [word_writeW_self, RegUpd.gpr_write_self]; rfl
  · exact TableFrame.table (((Outside.refl base DCOUNT 8 _).writeW (by decide) (by decide) (by decide) _).mono
      (by decide) (by decide))

/-- The decoded point (in slots 0–3) to entry `c` of the table at byte 7424, and the count
`c` down; `x19` keeps `c`. -/
theorem decodeStore_ok {s : State} {base : Addr} (hs : Scr s base) {c : Nat} (hc : c < 2)
    (hw : word s.mem base DCOUNT = BitVec.ofNat 64 c) :
    WP isa (.block decodeStore) s fun t => VerifyKeep base s t ∧ t.gpr .x19 = BitVec.ofNat 64 c ∧
      t.gpr .x8 = 1 ∧ word t.mem base DCOUNT = BitVec.ofNat 64 c - 1 ∧
      tablePoint t.mem base (7424 + 128 * c) = point (env s.mem base) 0 1 2 3 ∧
      (c = 0 → tablePoint t.mem base 7552 = tablePoint s.mem base 7552) := by
  rw [decodeStore, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x19 DCOUNT (by decide) (by decide)) fun a ⟨a19, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok hsa.x0 7424 c (by omega) (a19.trans hw)) fun b ⟨b8, kb⟩ => ?_
  have hsb := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok hsb b8 (by omega) (by omega)) fun d ⟨dp, kd⟩ => ?_
  refine WP.mono (countTail_ok (kd.scratch hsb)) fun t ⟨t8, tg, trd, twr, tsp, tm⟩ => ?_
  have d19 : d.gpr .x19 = BitVec.ofNat 64 c := by
    rw [kd.gpr _ (by decide), kb.gpr _ (by decide), a19]; exact hw
  have ft : Outside base DCOUNT 8 d.mem t.mem := by
    rw [tm]; exact (Outside.refl base DCOUNT 8 _).writeW (by decide) (by decide) (by decide) _
  have kdt : VerifyKeep base d t :=
    ⟨fun r _ _ hr => tg r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)), trd, twr, tsp,
      TableFrame.table (ft.mono (by decide) (by decide))⟩
  have hbs : ∀ d', tablePoint b.mem base d' = tablePoint s.mem base d' := fun d' => by rw [kb.mem, ka.mem]
  refine ⟨(PowersKeep.of_keeps ka (by decide)).trans ((PowersKeep.of_keeps kb (by decide)).trans
    ((PowersKeep.of_table kd (by omega) (by omega)).trans kdt)), ?_, t8, ?_, ?_, fun h0 => ?_⟩
  · rw [tg _ (by decide) (by decide), d19]
  · rw [tm, word_writeW_self, d19]
  · rw [(TableFrame.table ft).point (by omega) (Or.inl (by unfold DCOUNT; omega)) (by omega), dp, kb.mem, ka.mem]
  · subst h0
    rw [(TableFrame.table ft).point (by decide) (Or.inl (by decide)) (by decide),
      (TableFrame.table kd.mem).point (by decide) (Or.inr (by decide)) (by decide), hbs]

/-! ### One pass -/

/-- The encoding of pass `c`: `A`'s (`c = 0`), then `R`'s. -/
def inPtr (pk sig : Addr) (c : Nat) : Addr := if c = 0 then pk else sig

/-- The bytes of pass `c`'s encoding. -/
def inBytes (pkbs rbs : List Byte) (c : Nat) : List Byte := if c = 0 then pkbs else rbs

theorem VerifyPublic.pass {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr} {s : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) {c : Nat} (hc : c < 2) :
    word s.mem base (7936 + 8 * c) = inPtr pk sig c ∧
      (∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (inPtr pk sig c) d) 8) ∧
      Spec.Ed25519.bytesAt s.mem (inPtr pk sig c) 32 = inBytes pkbs rbs c := by
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · exact ⟨h.context.pkHeader, h.context.pkRead, h.pkBytes⟩
  · exact ⟨h.context.sigHeader, h.context.rRead, h.rBytes⟩

/-- After pass `c`, from `s`, whose encoding decodes to `p`: 0 in `x19` and `x8` if `p` is not a
point; else `c` in `x19`, 1 in `x8`, the count down, the point in entry `c` and, after `A`, `R`'s
entry kept. -/
def PassPost (base : Addr) (p : Option Spec.Ed25519.Point) (c : Nat) (s t : State) : Prop :=
  match p with
  | none => t.gpr .x19 = 0 ∧ t.gpr .x8 = 0
  | some q => t.gpr .x19 = BitVec.ofNat 64 c ∧ t.gpr .x8 = 1 ∧
      word t.mem base DCOUNT = BitVec.ofNat 64 c - 1 ∧ tablePoint t.mem base (7424 + 128 * c) = q ∧
      (c = 0 → tablePoint t.mem base 7552 = tablePoint s.mem base 7552)

theorem decodeBody_ok {s : State} {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr}
    {c : Nat} (hc : c < 2) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s)
    (hw : word s.mem base DCOUNT = BitVec.ofNat 64 c) :
    WP isa decodeBody s fun t => VerifyKeep base s t ∧
      PassPost base (Spec.Ed25519.decodePoint (inBytes pkbs rbs c)) c s t := by
  obtain ⟨hp, hr, hb⟩ := h.pass hc
  have hs := h.context.scratch
  rw [decodeBody]
  refine WP.seq (WP.mono (decodePtr_ok hs hc hw) fun a ⟨_, a2, ka⟩ => ?_)
  have hsa := hs.of_keeps ka (by decide)
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := inPtr pk sig c) hsa (a2.trans hp)
    (by rw [ka.rd, ka.wr]; exact hr)
  rw [ka.mem, hb] at hd
  generalize Spec.Ed25519.decodePoint (inBytes pkbs rbs c) = q at hd
  with_reducible apply WP.mono hd
  intro b hb'
  have kb := hb'.1
  have br := hb'.2
  have kab : VerifyKeep base s b := (PowersKeep.of_keeps ka (by decide)).trans (PowersKeep.of_decode kb)
  have hsb := kab.scratch hs
  cases q with
  | none =>
    have b8 : b.gpr .x8 = 0 := br
    refine WP.ite false (by simp only [eval, read_x, b8]; rfl) (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.mono (decodeFail_ok b) fun t ⟨t8, t19, kt⟩ =>
      ⟨kab.trans (PowersKeep.of_keeps kt (by decide)), t19, t8⟩
  | some q =>
    obtain ⟨b8, bp⟩ := br
    refine WP.ite true (by simp only [eval, read_x, b8]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    have bw : word b.mem base DCOUNT = BitVec.ofNat 64 c := by
      rw [(TableFrame.workspace (o := 0) (n := 0) kb.mem).word (by decide) (Or.inr (by decide)) (by decide),
        ka.mem]
      exact hw
    refine WP.mono (decodeStore_ok hsb hc bw) fun t ⟨kt, t19, t8, tw, tp, t7⟩ =>
      ⟨kab.trans kt, t19, t8, tw, tp.trans bp, fun h0 => (t7 h0).trans ?_⟩
    rw [workspace_tablePoint kb.mem (by decide) (by decide), ka.mem]

/-! ### The loop -/

/-- Before the pass with the count `n - 1`: after `R`'s (`n = 1`), `R` is a point, in its
entry. -/
def LInv (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) (n : Nat) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧ word s.mem base DCOUNT = BitVec.ofNat 64 (n - 1) ∧
    (n = 1 ∨ n = 2) ∧ (n = 1 → ∃ r, Spec.Ed25519.decodePoint rbs = some r ∧ tablePoint s.mem base 7552 = r)

/-- After the loop: 1 in `x8` and both points in their entries if both are points, else 0. -/
def DecodedPair (base : Addr) (a r : Option Spec.Ed25519.Point) (t : State) : Prop :=
  match a, r with
  | some a, some r => t.gpr .x8 = 1 ∧ tablePoint t.mem base 7424 = a ∧ tablePoint t.mem base 7552 = r
  | _, _ => t.gpr .x8 = 0

theorem DecodedPair.flag {base : Addr} {a r : Option Spec.Ed25519.Point} {t : State}
    (h : DecodedPair base a r t) : t.gpr .x8 = signWord (a.isSome && r.isSome) := by
  cases a <;> cases r
  all_goals first | exact h.1 | exact h

theorem decodeStep_ok {s : State} {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr} {n : Nat}
    (h : LInv base pk sig challenge pkbs rbs sbs kbs T n s) :
    WP isa decodeBody s fun t => VerifyKeep base s t ∧ VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t ∧
      eval (.nonzero .x .x19) t = some (n == 2 && (Spec.Ed25519.decodePoint rbs).isSome) ∧
      ((n == 2 && (Spec.Ed25519.decodePoint rbs).isSome) = true → LInv base pk sig challenge pkbs rbs sbs kbs T 1 t) ∧
      ((n == 2 && (Spec.Ed25519.decodePoint rbs).isSome) = false →
        DecodedPair base (Spec.Ed25519.decodePoint pkbs) (Spec.Ed25519.decodePoint rbs) t) := by
  obtain ⟨hp, hw, hn, hr⟩ := h
  rcases hn with rfl | rfl
  · obtain ⟨r, hr, tr⟩ := hr rfl
    refine WP.mono_syms (decodeBody_ok (c := 0) (by decide) hp hw) fun t ⟨kt, pt⟩ sy => ?_
    change PassPost base (Spec.Ed25519.decodePoint pkbs) 0 s t at pt
    rw [hr]
    refine ⟨kt, hp.of_keep kt sy, ?_, (fun h => by cases h), fun _ => ?_⟩
    · generalize Spec.Ed25519.decodePoint pkbs = pa at pt
      cases pa with
      | none => simp only [eval, read_x, pt.1]; rfl
      | some a => simp only [eval, read_x, pt.1]; rfl
    · generalize Spec.Ed25519.decodePoint pkbs = pa at pt
      cases pa with
      | none => exact pt.2
      | some a => exact ⟨pt.2.1, pt.2.2.2.1, (pt.2.2.2.2 rfl).trans tr⟩
  · refine WP.mono_syms (decodeBody_ok (c := 1) (by decide) hp hw) fun t ⟨kt, pt⟩ sy => ?_
    change PassPost base (Spec.Ed25519.decodePoint rbs) 1 s t at pt
    refine ⟨kt, hp.of_keep kt sy, ?_⟩
    generalize hpr : Spec.Ed25519.decodePoint rbs = pr at pt
    cases pr with
    | none =>
      refine ⟨by simp only [eval, read_x, pt.1]; rfl, (fun h => by cases h), fun _ => ?_⟩
      cases Spec.Ed25519.decodePoint pkbs <;> exact pt.2
    | some r =>
      refine ⟨by simp only [eval, read_x, pt.1]; rfl, fun _ => ?_, (fun h => by cases h)⟩
      exact ⟨hp.of_keep kt sy, pt.2.2.1, Or.inl rfl, fun _ => ⟨r, hpr, pt.2.2.2.1⟩⟩

theorem decodeLoop_ok {s : State} {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr}
    (h : LInv base pk sig challenge pkbs rbs sbs kbs T 2 s) :
    WP isa (.loop decodeBody (.nonzero .x .x19)) s fun t => VerifyKeep base s t ∧
      DecodedPair base (Spec.Ed25519.decodePoint pkbs) (Spec.Ed25519.decodePoint rbs) t := by
  refine WP.loop (M := isa) (fun (n : Nat) (x : State) => LInv base pk sig challenge pkbs rbs sbs kbs T n x ∧
    VerifyKeep base s x) ?_ 2 s ⟨h, PowersKeep.refl base 56 7752 s⟩
  intro n x hx
  refine WP.mono (decodeStep_ok hx.1) fun t ⟨kt, _, ev, ht, hf⟩ => ?_
  cases hb : (n == 2 && (Spec.Ed25519.decodePoint rbs).isSome)
  · exact Or.inl ⟨ev.trans (by rw [hb]), hx.2.trans kt, hf hb⟩
  · have hn : n = 2 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact hb.1
    exact Or.inr ⟨ev.trans (by rw [hb]), 1, by omega, ht hb, hx.2.trans kt⟩

/-! ### Constant time -/

theorem agree_x0_x19 {x y : State} (h0 : x.gpr .x0 = y.gpr .x0) (h19 : x.gpr .x19 = y.gpr .x19) :
    ∀ r ∈ Taint.ofRegs [.x0, .x19], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h0, h19]

/-- A block that loads the count, the same `c` in both runs, into `x19`, and then forms
addresses from `x0` and `x19` alone. -/
theorem countThen_ct {P : State → Prop} {base : Addr} {c : Nat}
    (hP : ∀ x, P x → Scr x base ∧ word x.mem base DCOUNT = BitVec.ofNat 64 c) {ys : List Instr}
    (hy : CT (fun x y => x.gpr .x0 = base ∧ y.gpr .x0 = base ∧ x.gpr .x19 = y.gpr .x19) (.block ys)
      (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) (.block ([ld .x19 DCOUNT] ++ ys)) (fun _ _ => True) := by
  have h1 : CT (fun x y => P x ∧ P y) (.block [ld .x19 DCOUNT]) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree (hP _ h.1).1.x0 (hP _ h.2).1.x0) (by taint_decide)
  have w (x : State) (hx : P x) : WP isa (.block [ld .x19 DCOUNT]) x fun t =>
      t.gpr .x0 = base ∧ t.gpr .x19 = BitVec.ofNat 64 c :=
    WP.mono (loadPointer_ok (hP x hx).1 .x19 DCOUNT (by decide) (by decide)) fun t ⟨t19, kt⟩ =>
      ⟨(kt.gpr _ (by decide)).trans (hP x hx).1.x0, t19.trans (hP x hx).2⟩
  exact blockAppend_ct ((CT.wp h1 fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩) hy

theorem decodeBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) {c : Nat} (hc : c < 2) :
    CT (fun x y => (VerifyPublic base pk sig challenge pkbs rbs sbs kbs T x ∧
      word x.mem base DCOUNT = BitVec.ofNat 64 c) ∧ (VerifyPublic base pk sig challenge pkbs rbs sbs kbs T y ∧
      word y.mem base DCOUNT = BitVec.ofNat 64 c)) decodeBody (fun _ _ => True) := by
  let P : State → Prop := fun x =>
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs T x ∧ word x.mem base DCOUNT = BitVec.ofNat 64 c
  let p := inPtr pk sig c
  let bs := inBytes pkbs rbs c
  have ptrCT : CT (fun x y => P x ∧ P y) (.block decodePtr) (fun _ _ => True) :=
    countThen_ct (ys := [.lsl .x .x2 .x19 3, .add .x .x2 .x2 .x0, .ldr .x .x2 .x2 7936])
      (fun x hx => ⟨hx.1.context.scratch, hx.2⟩)
      (CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree_x0_x19 (h.1.trans h.2.1.symm) h.2.2)
        (by taint_decide))
  have ptrW (x : State) (hx : P x) : WP isa (.block decodePtr) x fun t => P t ∧ DecodeCTPre base p bs t := by
    obtain ⟨hp, hr, hb⟩ := hx.1.pass hc
    refine WP.mono_syms (decodePtr_ok hx.1.context.scratch hc hx.2) fun t ⟨_, t2, kt⟩ sy => ?_
    have kp : VerifyKeep base x t := PowersKeep.of_keeps kt (by decide)
    exact ⟨⟨hx.1.of_keep kp sy, by rw [kt.mem]; exact hx.2⟩, kp.scratch hx.1.context.scratch, t2.trans hp,
      by rw [kt.rd, kt.wr]; exact hr, by rw [kt.mem]; exact hb⟩
  have hl := CT.wp ptrCT fun x y h => ⟨ptrW x h.1, ptrW y h.2⟩
  have decCT := (pointDecode_ct base p bs).mono
    (fun x y (h : (P x ∧ DecodeCTPre base p bs x) ∧ (P y ∧ DecodeCTPre base p bs y)) => ⟨h.1.2, h.2.2⟩)
    (fun _ _ h => h)
  have decW (x : State) (hx : P x ∧ DecodeCTPre base p bs x) :
      WP isa pointDecode x fun t => P t ∧ DecodeResult base (Spec.Ed25519.decodePoint bs) t := by
    have hd := pointDecode_ok (base := base) (p := p) hx.2.1 hx.2.2.1 hx.2.2.2.1
    rw [hx.2.2.2.2] at hd
    with_reducible apply WP.mono_syms hd
    intro t ht sy
    refine ⟨⟨hx.1.1.of_keep (PowersKeep.of_decode ht.1) sy, ?_⟩, ht.2⟩
    rw [(TableFrame.workspace (o := 0) (n := 0) ht.1.mem).word (by decide) (Or.inr (by decide)) (by decide)]
    exact hx.1.2
  have hd := CT.wp decCT fun x y h => ⟨decW x h.1, decW y h.2⟩
  rw [decodeBody]
  refine CT.seq (hl.mono (fun _ _ h => h) (fun _ _ h => h.2)) (CT.seq (hd.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (CT.ite ?_ ?_ ?_))
  · intro x y h
    simp only [eval, read_x, decodeResult_flag h.1.2, decodeResult_flag h.2.2]
  · rw [decodeStore, List.append_assoc, List.append_assoc]
    refine countThen_ct (P := fun x => P x ∧ DecodeResult base (Spec.Ed25519.decodePoint bs) x)
      (fun x hx => ⟨hx.1.1.context.scratch, hx.1.2⟩)
      (CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree_x0_x19 (h.1.trans h.2.1.symm) h.2.2)
        (by taint_decide)) |>.mono
      (fun _ _ h => h.1) (fun _ _ h => h)
  · exact (CT.taint (Taint.ofRegs []) (fun _ _ _ => agree_ofRegs (by simp)) (by taint_decide) :
      CT (fun _ _ => True) (.block decodeFail) (fun _ _ => True)).mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeLoop_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) :
    CT (fun x y => LInv base pk sig challenge pkbs rbs sbs kbs T 2 x ∧ LInv base pk sig challenge pkbs rbs sbs kbs T 2 y)
      (.loop decodeBody (.nonzero .x .x19)) (fun x y =>
        (VerifyPublic base pk sig challenge pkbs rbs sbs kbs T x ∧
          DecodedPair base (Spec.Ed25519.decodePoint pkbs) (Spec.Ed25519.decodePoint rbs) x) ∧
        (VerifyPublic base pk sig challenge pkbs rbs sbs kbs T y ∧
          DecodedPair base (Spec.Ed25519.decodePoint pkbs) (Spec.Ed25519.decodePoint rbs) y)) := by
  refine CT.loop (fun n x y => LInv base pk sig challenge pkbs rbs sbs kbs T n x ∧
    LInv base pk sig challenge pkbs rbs sbs kbs T n y) (fun n => ?_) 2
  have hb : CT (fun x y => LInv base pk sig challenge pkbs rbs sbs kbs T n x ∧
      LInv base pk sig challenge pkbs rbs sbs kbs T n y) decodeBody (fun _ _ => True) := by
    by_cases hn : n - 1 < 2
    · exact (decodeBody_ct base pk sig challenge pkbs rbs sbs kbs T hn).mono
        (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) (fun _ _ h => h)
    · exact CT.of_false fun x y h => hn (by rcases h.1.2.2.1 with rfl | rfl <;> decide)
  refine (CT.wp hb fun x y h => ⟨WP.mono (decodeStep_ok h.1) fun _ h => h.2,
    WP.mono (decodeStep_ok h.2) fun _ h => h.2⟩).mono (fun _ _ h => h)
    fun x y ⟨_, ⟨px, ex, tx, fx⟩, ⟨py, ey, ty, fy⟩⟩ => ⟨ex.trans ey.symm, fun hf => ?_, fun ht => ?_⟩
  · have hb : (n == 2 && (Spec.Ed25519.decodePoint rbs).isSome) = false := Option.some.inj (ex.symm.trans hf)
    exact ⟨⟨px, fx hb⟩, ⟨py, fy hb⟩⟩
  · have hb : (n == 2 && (Spec.Ed25519.decodePoint rbs).isSome) = true := Option.some.inj (ex.symm.trans ht)
    have hn : n = 2 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact hb.1
    exact ⟨1, by omega, tx hb, ty hb⟩

/-! ### Decoding, then the equation -/

def equationWithR (r : Option Spec.Ed25519.Point) (a : Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match r with
  | none => false
  | some r => Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul challenge a))

def decodedEquation (a r : Option Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match a with
  | none => false
  | some a => equationWithR r a scalar challenge

theorem decodeStartPub_ok {s : State} {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) :
    WP isa (.block [.movz .w .x19 1 0, st .x19 DCOUNT]) s fun t =>
      VerifyKeep base s t ∧ LInv base pk sig challenge pkbs rbs sbs kbs T 2 t :=
  WP.mono_syms (decodeStart_ok h.context.scratch) fun _ ⟨tw, kt⟩ sy =>
    ⟨kt, h.of_keep kt sy, tw, Or.inr rfl, fun h => absurd h (by decide)⟩

theorem verifyDecode_wp {s : State} {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) :
    WP isa verifyDecode s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (decodedEquation (Spec.Ed25519.decodePoint pkbs) (Spec.Ed25519.decodePoint rbs)
        (Spec.Ed25519.decodeLE sbs) (Spec.Ed25519.decodeLE kbs)) := by
  rw [verifyDecode, decodeBoth]
  refine WP.seq (WP.seq (WP.mono_syms (decodeStartPub_ok h) fun a ⟨ka, ha⟩ sya =>
    WP.mono_syms (decodeLoop_ok ha) fun b ⟨kb, pb⟩ syb => ?_))
  have kab := ka.trans kb
  have hb := h.of_keep kab (by rw [syb, sya])
  have fail (hz : b.gpr .x8 = 0) (hd : decodedEquation (Spec.Ed25519.decodePoint pkbs)
      (Spec.Ed25519.decodePoint rbs) (Spec.Ed25519.decodeLE sbs) (Spec.Ed25519.decodeLE kbs) = false) :
      WP isa (decodedThen verifyEquationPoints) b fun t => VerifyKeep base s t ∧
        t.gpr .x8 = signWord (decodedEquation (Spec.Ed25519.decodePoint pkbs) (Spec.Ed25519.decodePoint rbs)
          (Spec.Ed25519.decodeLE sbs) (Spec.Ed25519.decodeLE kbs)) := by
    rw [decodedThen]
    refine WP.ite false (by simp only [eval, read_x, hz]; rfl) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.mono (recoverInvalid_ok b base) fun t ⟨kt, tr⟩ => ⟨kab.trans (PowersKeep.of_keep kt), ?_⟩
    rw [hd]; exact tr
  generalize ha : Spec.Ed25519.decodePoint pkbs = pa at pb fail
  generalize hr : Spec.Ed25519.decodePoint rbs = pr at pb fail
  cases pa with
  | none => exact fail pb rfl
  | some a =>
    cases pr with
    | none => exact fail pb rfl
    | some r =>
      obtain ⟨b8, ba, br⟩ := pb
      rw [decodedThen]
      refine WP.ite true (by simp only [eval, read_x, b8]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
      obtain ⟨Aa, hA⟩ := decodePoint_rep ha
      obtain ⟨Ra, hR⟩ := decodePoint_rep hr
      refine WP.mono (verifyEquationPoints_ok hb.context.scratch hb.context.sigHeader hb.context.challengeHeader
        hb.context.scalarQ hb.context.scalarFar hb.context.challengeQ hb.context.challengeFar
        (by rw [ba]; exact hA) (by rw [br]; exact hR) hb.context.tbl) fun t ⟨kt, tv⟩ => ⟨kab.trans kt, ?_⟩
      rw [tv, ba, br, hb.sBytes, hb.kBytes]
      rfl

theorem verifyDecode_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) :
    CT (fun x y => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T x ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T y) verifyDecode (fun _ _ => True) := by
  have startCT : CT (fun x y => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T x ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T y) (.block [.movz .w .x19 1 0, st .x19 DCOUNT])
      (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.context.scratch.x0 h.2.context.scratch.x0)
      (by taint_decide)
  have hs := CT.wp startCT fun x y h => ⟨WP.mono (decodeStartPub_ok h.1) fun _ h => h.2,
    WP.mono (decodeStartPub_ok h.2) fun _ h => h.2⟩
  rw [verifyDecode, decodeBoth, decodedThen]
  refine CT.seq (CT.seq (hs.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (decodeLoop_ct base pk sig challenge pkbs rbs sbs kbs T)) (CT.ite ?_ ?_ ?_)
  · intro x y h
    simp only [eval, read_x, h.1.2.flag, h.2.2.flag]
  · have none8 : ∀ {a r : Option Spec.Ed25519.Point}, (a.isSome && r.isSome) = false →
        CT (fun x y => ((VerifyPublic base pk sig challenge pkbs rbs sbs kbs T x ∧ DecodedPair base a r x) ∧
          (VerifyPublic base pk sig challenge pkbs rbs sbs kbs T y ∧ DecodedPair base a r y)) ∧
          eval (.nonzero .x .x8) x = some true) verifyEquationPoints (fun _ _ => True) :=
      fun hn => CT.of_false fun x y h => by
        have he := h.2
        simp only [eval, read_x, h.1.1.2.flag, hn] at he
        exact absurd he (by decide)
    generalize ha : Spec.Ed25519.decodePoint pkbs = pa
    generalize hr : Spec.Ed25519.decodePoint rbs = pr
    cases pa with
    | none => exact none8 rfl
    | some a =>
      cases pr with
      | none => exact none8 rfl
      | some r =>
        obtain ⟨Aa, hA⟩ := decodePoint_rep ha
        obtain ⟨Ra, hR⟩ := decodePoint_rep hr
        exact (verifyEquationPoints_ct base pk sig challenge pkbs rbs sbs kbs T a r hA hR).mono
          (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.2⟩, ⟨h.1.2.1, h.1.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem verifyBody_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) :
    CT (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecode recoverInvalid)) (fun _ _ => True) := by
  let P := VerifyPublic base pk sig challenge pkbs rbs sbs kbs T
  have ht := (verifyScalar_ct base pk sig challenge).mono
    (fun _ _ (h : P _ ∧ P _) => ⟨h.1.context, h.2.context⟩) (fun _ _ h => h)
  have hw (s : State) (h : P s) : WP isa (.block verifyScalar) s fun t =>
      P t ∧ eval (.nonzero .x .x8) t = some (decide (Spec.Ed25519.decodeLE sbs < Spec.Ed25519.L)) := by
    refine WP.mono_syms (verifyScalar_ok h.context.scratch h.context.sigHeader h.context.scalarRead)
      fun t ⟨kt, _, tc⟩ sy => ?_
    exact ⟨h.of_keep (PowersKeep.of_keep kt) sy, by change some (t.gpr .x8 != 0) = _; rw [tc, h.sBytes]⟩
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (verifyDecode_ct base pk sig challenge pkbs rbs sbs kbs T).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
