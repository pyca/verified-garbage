import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Setup
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Poly1305 on AArch64 in AdvSIMD: saving registers, the accumulator, the constants

Untrusted: everything here is checked by Lean. `save` stores the low halves of
`v8`–`v14` in the state's working space (bytes 72–127) and `restore` loads
them back; `loadH` puts the accumulator's limbs in lane 0 of `H` (lane 1
zero); `times5 R S` makes `S j` five times `R j`.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)

/-! ## `5 R` -/

theorem times5_aux (R S : Nat → VReg) (hRS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → R i ≠ S j)
    (hS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → i ≠ j → S i ≠ S j) :
    ∀ (js : List Nat), (∀ j ∈ js, 1 ≤ j ∧ j < 5) → js.Nodup → ∀ s : State,
      (∀ j ∈ js, ∀ c < 4, wd (s.v (R j)) c < 2 ^ 29) →
      WP isa (.block (js.flatMap fun j =>
          [vo (.shift .shl .s4 (S j) (R j) 2), vo (.add .s4 (S j) (S j) (R j))])) s fun t =>
        (∀ j ∈ js, ∀ c < 4, wd (t.v (S j)) c = 5 * wd (s.v (R j)) c) ∧
        (∀ r, (∀ j ∈ js, r ≠ S j) → t.v r = s.v r) ∧
        t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  intro js
  induction js with
  | nil =>
    intro _ _ s _
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    intro hjs hnd s hb
    obtain ⟨hj1, hj5⟩ := hjs j List.mem_cons_self
    have hjs' : ∀ k ∈ js, 1 ≤ k ∧ k < 5 := fun k hk => hjs k (List.mem_cons_of_mem _ hk)
    obtain ⟨hnj, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    have nRS := hRS j hj5 hj1 j hj5 hj1
    rw [RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ nRS]
    set u := (s.setV (S j) (VArr.s4.map2 (fun w x y => VShiftOp.shl.eval 2 w x y) (s.v (S j)) (s.v (R j)))).setV
      (S j) (VArr.s4.map2 (fun _ a b => a + b)
        (VArr.s4.map2 (fun w x y => VShiftOp.shl.eval 2 w x y) (s.v (S j)) (s.v (R j))) (s.v (R j))) with hu
    have uR : ∀ k ∈ js, u.v (R k) = s.v (R k) := fun k hk => by
      have hk := hjs' k hk
      rw [hu, RegUpd.v_setV_of_ne _ _ (hRS k hk.2 hk.1 j hj5 hj1),
        RegUpd.v_setV_of_ne _ _ (hRS k hk.2 hk.1 j hj5 hj1)]
    refine WP.mono (ih hjs' hnd' u fun k hk c hc => by rw [uR k hk]; exact hb k (List.mem_cons_of_mem _ hk) c hc)
      fun t ⟨h5, hv, hg, hm, hrd, hwr, hsp⟩ => ⟨fun k hk c hc => ?_, fun r hr => ?_, hg, hm, hrd, hwr, hsp⟩
    · rcases List.mem_cons.mp hk with rfl | hk'
      · rw [hv _ fun l hl => hS k hj5 hj1 l (hjs' l hl).2 (hjs' l hl).1 fun h => hnj (h ▸ hl), hu,
          RegUpd.v_setV_self]
        exact wd_times5 _ _ hc (hb k List.mem_cons_self c hc)
      · rw [h5 k hk' c hc, uR k hk']
    · rw [hv r fun l hl => hr l (List.mem_cons_of_mem _ hl), hu,
        RegUpd.v_setV_of_ne _ _ (hr j List.mem_cons_self), RegUpd.v_setV_of_ne _ _ (hr j List.mem_cons_self)]

theorem times5_ok (R S : Nat → VReg) (hRS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → R i ≠ S j)
    (hS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → i ≠ j → S i ≠ S j) (s : State)
    (hb : ∀ j < 5, 1 ≤ j → ∀ c < 4, wd (s.v (R j)) c < 2 ^ 29) :
    WP isa (.block (times5 R S)) s fun t =>
      (∀ j < 5, 1 ≤ j → ∀ c < 4, wd (t.v (S j)) c = 5 * wd (s.v (R j)) c) ∧
      (∀ r, (∀ j < 5, 1 ≤ j → r ≠ S j) → t.v r = s.v r) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hmem : ∀ j, j ∈ [1, 2, 3, 4] ↔ 1 ≤ j ∧ j < 5 := by
    intro j; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  refine WP.mono (times5_aux R S hRS hS [1, 2, 3, 4] (fun j hj => (hmem j).mp hj) (by decide) s
    fun j hj => hb j ((hmem j).mp hj).2 ((hmem j).mp hj).1)
    fun t ⟨h5, hv, hk⟩ => ⟨fun j hj h1 => h5 j ((hmem j).mpr ⟨h1, hj⟩),
      fun r hr => hv r fun j hj => hr j ((hmem j).mp hj).2 ((hmem j).mp hj).1, hk⟩

/-! ## Saving and restoring `v8`–`v14` -/

/-- The slot of `v(8 + k)`. -/
abbrev svA (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (72 + 8 * k)

/-- The slots. -/
abbrev svR (st : Addr) : Region := ⟨st + BitVec.ofNat 64 72, 56⟩

theorem readW_write8 (m : Mem) (a : Addr) (v : BitVec 64) : (m.write a 8 v).readW a 64 = v := by
  have := Mem.readW_writeW_self m a 8 v (by decide)
  simpa only [Mem.writeW, BitVec.setWidth_eq] using this

theorem readW_write8_sep {m : Mem} {a b : Addr} (h : Mem.Sep a 8 b 8) (v : BitVec (8 * 8)) :
    (m.write b 8 v).readW a 64 = m.readW a 64 := by
  simp only [Mem.readW]
  rw [Mem.read_write_sep h (by decide)]

theorem svA_sep (st : Addr) {j k : Nat} (hj : j < 7) (hk : k < 7) (h : j ≠ k) :
    Mem.Sep (svA st j) 8 (svA st k) 8 := Offset.sep st (by omega) (by omega) (by omega)

theorem svA_in (st : Addr) {k : Nat} (hk : k < 7) : (svR st).Contains (svA st k) 8 :=
  Offset.contains st (by omega) (by omega) (by omega)

theorem save_aux (st : Addr) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < 7) → ks.Nodup → ∀ s : State, s.gpr .x0 = st →
      (∀ k ∈ ks, InRegions s.wr (svA st k) 8) →
      WP isa (.block (ks.flatMap fun k => [.umov .x .x9 (V (8 + k)) 0, .str .x .x9 .x0 (72 + 8 * k)])) s
        fun t => (∀ k ∈ ks, t.mem.readW (svA st k) 64 = vdword (s.v (V (8 + k))) 0) ∧
          (∀ k < 7, k ∉ ks → t.mem.readW (svA st k) 64 = s.mem.readW (svA st k) 64) ∧
          Frame [svR st] s.mem t.mem ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
          t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  intro ks
  induction ks with
  | nil =>
    intro _ _ s _ _
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, Frame.refl _ _,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro hks hnd s hx0 hw
    have hk : k < 7 := hks k List.mem_cons_self
    have hks' : ∀ j ∈ ks, j < 7 := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine WP.block_cons_iff.mpr ⟨_, exec_umov s .x9 (V (8 + k)) (by decide), ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_str ⟨by omega, by omega⟩ (by
      simp only [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x0 = Reg.x9 by decide), hx0]
      exact hw k List.mem_cons_self), ?_⟩
    simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x0 = Reg.x9 by decide), hx0,
      RegUpd.mem_write, Size.bits, BitVec.setWidth_eq]
    set u : State := { s.write .x .x9 (vdword (s.v (V (8 + k))) 0) with
      mem := s.mem.write (svA st k) 8 (vdword (s.v (V (8 + k))) 0) } with hu
    have ux0 : u.gpr .x0 = st := by
      show (s.write .x .x9 (vdword (s.v (V (8 + k))) 0)).gpr .x0 = st
      rw [RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x0 = Reg.x9 by decide)]; exact hx0
    refine WP.mono (ih hks' hnd' u ux0 fun j hj => hw j (List.mem_cons_of_mem _ hj))
      fun t ⟨hs, hn, hf, hg, hv, hrd, hwr, hsp⟩ => ⟨fun j hj => ?_, fun j hj hjn => ?_, ?_, fun r hr => ?_,
        hv, hrd, hwr, hsp⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · rw [hn j hk hnk, hu]; exact readW_write8 _ _ _
      · rw [hs j hj', hu]; rfl
    · have hjk : j ≠ k := fun h => hjn (h ▸ List.mem_cons_self)
      rw [hn j hj (fun h => hjn (List.mem_cons_of_mem _ h)), hu]
      exact readW_write8_sep (svA_sep st hj hk hjk) _
    · exact ((Frame.refl _ _).write List.mem_cons_self _ (svA_in st hk)).trans hf
    · rw [hg r hr]
      show (s.write .x .x9 (vdword (s.v (V (8 + k))) 0)).gpr r = s.gpr r
      exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem save_ok (s : State) (hw : ∀ k < 7, InRegions s.wr (svA (s.gpr .x0) k) 8) :
    WP isa (.block save) s fun t =>
      (∀ k < 7, t.mem.readW (svA (s.gpr .x0) k) 64 = vdword (s.v (V (8 + k))) 0) ∧
      Frame [svR (s.gpr .x0)] s.mem t.mem ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  WP.mono (save_aux (s.gpr .x0) (List.range 7) (fun _ h => List.mem_range.mp h) List.nodup_range s rfl
    fun k hk => hw k (List.mem_range.mp hk))
    fun _ ⟨h, _, k⟩ => ⟨fun k hk => h k (List.mem_range.mpr hk), k⟩

theorem V8_ne : ∀ j < 7, ∀ k < 7, j ≠ k → V (8 + j) ≠ V (8 + k) := by decide

theorem restore_aux (st : Addr) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < 7) → ks.Nodup → ∀ s : State, s.gpr .x0 = st →
      (∀ k ∈ ks, InRegions (s.rd ++ s.wr) (svA st k) 8) →
      WP isa (.block (ks.flatMap fun k => [.ldr .x .x9 .x0 (72 + 8 * k), vo (.ins .d2 (V (8 + k)) 0 .x9)])) s
        fun t => (∀ k ∈ ks, vdword (t.v (V (8 + k))) 0 = s.mem.readW (svA st k) 64) ∧
          (∀ r, (∀ k ∈ ks, r ≠ V (8 + k)) → t.v r = s.v r) ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧
          t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  intro ks
  induction ks with
  | nil =>
    intro _ _ s _ _
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro hks hnd s hx0 hr
    have hk : k < 7 := hks k List.mem_cons_self
    have hks' : ∀ j ∈ ks, j < 7 := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine WP.block_cons_iff.mpr ⟨_, exec_ldr ⟨by omega, by omega⟩ (by rw [hx0]; exact hr k List.mem_cons_self), ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    set u := (s.write .x .x9 (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (72 + 8 * k)) 8)).setV (V (8 + k))
      (setLane ((s.write .x .x9 (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (72 + 8 * k)) 8)).v (V (8 + k))) 64 0
        ((s.write .x .x9 (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (72 + 8 * k)) 8)).gpr .x9)) with hu
    have ug : ∀ r, r ≠ .x9 → u.gpr r = s.gpr r := fun r hr => by
      rw [hu, RegUpd.gpr_setV]; exact RegUpd.gpr_write_of_ne _ _ _ hr
    have um : u.mem = s.mem := rfl
    refine WP.mono (ih hks' hnd' u (by rw [ug _ (by decide)]; exact hx0) fun j hj => by
        rw [show u.rd = s.rd from rfl, show u.wr = s.wr from rfl]; exact hr j (List.mem_cons_of_mem _ hj))
      fun t ⟨hs, hv, hg, hm, hrd, hwr, hsp⟩ => ⟨fun j hj => ?_, fun r hr' => ?_, fun r hr' => ?_,
        hm.trans um, hrd, hwr, hsp⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · rw [hv _ fun l hl => V8_ne j hk l (hks' l hl) fun h => hnk (h ▸ hl), hu, RegUpd.v_setV_self,
          vdword_setLane _ (by decide) (by decide), ite_eq_left (rfl : 0 = 0), RegUpd.gpr_write_self, hx0]
        rfl
      · rw [hs j hj', um]
    · rw [hv r fun l hl => hr' l (List.mem_cons_of_mem _ hl), hu,
        RegUpd.v_setV_of_ne _ _ (hr' k List.mem_cons_self)]
      rfl
    · rw [hg r hr', ug r hr']

theorem restore_ok (s : State) (hr : ∀ k < 7, InRegions (s.rd ++ s.wr) (svA (s.gpr .x0) k) 8) :
    WP isa (.block restore) s fun t =>
      (∀ k < 7, vdword (t.v (V (8 + k))) 0 = s.mem.readW (svA (s.gpr .x0) k) 64) ∧
      (∀ r, (∀ k < 7, r ≠ V (8 + k)) → t.v r = s.v r) ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  WP.mono (restore_aux (s.gpr .x0) (List.range 7) (fun _ h => List.mem_range.mp h) List.nodup_range s rfl
    fun k hk => hr k (List.mem_range.mp hk))
    fun _ ⟨h, hv, k⟩ => ⟨fun k hk => h k (List.mem_range.mpr hk),
      fun r hr => hv r fun k hk => hr k (List.mem_range.mp hk), k⟩

/-! ## The accumulator into the vectors -/

theorem loadH_ok (s : State) (hm : (s.gpr .x16).toNat = 2 ^ 26 - 1) :
    WP isa (.block loadH) s fun t =>
      ((s.gpr .x6).toNat ≤ 4 → ∀ i < 5, ln (t.v (hV i)) 0 = limOf s i) ∧ (∀ i < 5, ln (t.v (hV i)) 1 = 0) ∧
      (∀ r, (∀ i < 5, r ≠ hV i) → t.v r = s.v r) ∧ (∀ r ∉ limbRegs, t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [loadH]
  refine WP.block_append (WP.mono (limbs_ok s hm) fun s1 ⟨l1, g1, v1, m1, rd1, wr1, sp1⟩ => ?_)
  simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil]
  iterate 10
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    vstep
  refine WP.block_nil_iff.mpr ⟨fun h6 i hi => ?_, fun i hi => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← l1 h6 i hi]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;> simp only [ln, vdword_setLane _ (show 0 < 2 by decide) (show 0 < 2 by decide), ite_true, X,
        RegUpd.gpr_setV]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;> simp only [ln, vdword_setLane _ (show 0 < 2 by decide) (show 1 < 2 by decide),
        show (1 : Nat) ≠ 0 by decide, ite_false] <;> rfl
  · have := hr 0 (by decide); have := hr 1 (by decide); have := hr 2 (by decide)
    have := hr 3 (by decide); have := hr 4 (by decide)
    simp (disch := assumption) only [RegUpd.v_setV_of_ne]
    exact congrFun v1 r
  · intro r hr; simp only [RegUpd.gpr_setV]; exact g1 r hr
  · simp only [RegUpd.mem_setV]; exact m1
  · simp only [RegUpd.rd_setV]; exact rd1
  · simp only [RegUpd.wr_setV]; exact wr1
  · simp only [RegUpd.sp_setV]; exact sp1

/-! ## The constants and the count -/

/-- Reads of every register through the writes so far. -/
macro "allstep" : tactic =>
  `(tactic| simp (disch := first | decide | with_reducible assumption) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne,
    RegUpd.gpr_setV, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.v_write, State.read, Size.bits,
    BitVec.setWidth_eq])

/-- The end of `setup`. -/
def tail : List Instr :=
  [vo (.dup .d2 maskV .x16), .movz .x .x9 0x100 1, vo (.dup .d2 padV .x9), .lsr .x .x9 .x3 6, .subImm .x .x9 .x9 1]

theorem tail_ok (s : State) :
    WP isa (.block tail) s fun t =>
      (∀ e < 2, ln (t.v maskV) e = (s.gpr .x16).toNat) ∧ (∀ e < 2, ln (t.v padV) e = 2 ^ 24) ∧
      t.gpr .x9 = (s.gpr .x3 >>> 6) - 1 ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧
      (∀ r, r ≠ maskV → r ≠ padV → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [tail]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_,
    rfl, rfl, rfl, rfl⟩
  · allstep
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · simp only [ln, vdword_ofVDwords_0]
    · simp only [ln, vdword_ofVDwords_1]
  · allstep
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · simp only [ln, vdword_ofVDwords_0]; rfl
    · simp only [ln, vdword_ofVDwords_1]; rfl
  · allstep; rfl
  · allstep
  · allstep

end VG.Proof.Poly1305.AArch64.Vector
