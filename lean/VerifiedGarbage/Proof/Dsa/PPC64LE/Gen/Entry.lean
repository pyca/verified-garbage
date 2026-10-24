module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: entry and exit

`entry_ok`: from the contract's precondition, `entry` saves our caller's
registers and our return address in `scratch`'s header, with `out`, the tapes'
pointers and lengths, and 0 for the witnesses read and the status: a state of
the search (`GI`). `restore_ok`: from a state of the search, `restore`
gives back our caller's registers and return address (`abiPreserved`).
Both rest on `stores_ok` and `loads_ok`, a list of stores or loads through
a base register.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

theorem write_write (s : State) (r : Reg) (a b : BitVec 64) : (s.write r a).write r b = s.write r b := by
  simp only [State.write]
  congr 1
  funext x
  split <;> rfl

/-- `addSp`. -/
theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 2 ^ 15) :
    exec (.addSp d imm) s = some (s.write d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ↓reduceIte]

/-- A list of stores of registers through `r11`, at distinct aligned offsets. -/
theorem stores_ok {B : Addr} : ∀ (L : List (Reg × Nat)) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr .r11 = B → (∀ p ∈ L, p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧ InRegions s.wr (B + BitVec.ofNat 64 p.2) 8) →
    (L.map Prod.snd).Nodup →
    (∀ t, t.gpr = s.gpr → t.sp = s.sp → t.lr = s.lr → t.rd = s.rd → t.wr = s.wr →
      (∀ p ∈ L, t.mem.readW (B + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) →
      Frame (L.map fun p => ⟨B + BitVec.ofNat 64 p.2, 8⟩) s.mem t.mem → WP isa (.block rest) t Q) →
    WP isa (.block (L.map (fun p => Instr.store .d p.1 .r11 p.2) ++ rest)) s Q
  | [], s, rest, Q, _, _, _, k => k s rfl rfl rfl rfl rfl (by simp) (Frame.refl _ _)
  | p :: L, s, rest, Q, hb, hok, hnd, k => by
    obtain ⟨o1, o2, o3⟩ := hok p List.mem_cons_self
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_map] at hnd ⊢
    refine wp_std' (by decide) ⟨o1, by omega⟩ (by rw [hb]) o3 fun s₁ m₁ sp₁ lr₁ => ?_
    refine stores_ok L s₁ rest Q (by rw [m₁.gpr, hb]) (fun q hq => ?_) hnd.2 fun t g sp lr rd wr rv f => ?_
    · obtain ⟨q1, q2, q3⟩ := hok q (List.mem_cons_of_mem _ hq)
      exact ⟨q1, q2, by rw [m₁.wr]; exact q3⟩
    refine k t (g.trans m₁.gpr) (sp.trans sp₁) (lr.trans lr₁) (rd.trans m₁.rd) (wr.trans m₁.wr) (fun q hq => ?_)
      ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [f.readW (r := ⟨B + BitVec.ofNat 64 q.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide),
          m₁.mem, Mem.readW_writeW_self64]
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
        have ne : q'.2 ≠ q.2 := fun e => hnd.1 ⟨q', hq', e⟩
        obtain ⟨a1, a2, _⟩ := hok q' (List.mem_cons_of_mem _ hq')
        exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · rw [rv q hq, m₁.gpr]
    · rw [m₁.mem] at f
      have f1 : Frame (⟨B + BitVec.ofNat 64 p.2, 8⟩ :: L.map fun q => ⟨B + BitVec.ofNat 64 q.2, 8⟩) s.mem
          (s.mem.writeW (B + BitVec.ofNat 64 p.2) (s.gpr p.1)) :=
        (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      exact f1.trans (f.mono fun r hr => List.mem_cons_of_mem _ hr)

/-- A list of loads of distinct registers other than `b` through `b`. -/
theorem loads_ok {B : Addr} {b : Reg} (hb0 : b ≠ .r0) :
    ∀ (L : List (Reg × Nat)) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr b = B → (∀ p ∈ L, p.1 ≠ b ∧ p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧
      InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 p.2) 8) →
    (L.map Prod.fst).Nodup →
    (∀ t, (∀ p ∈ L, t.gpr p.1 = s.mem.readW (B + BitVec.ofNat 64 p.2) 64) →
      (∀ r, r ∉ L.map Prod.fst → t.gpr r = s.gpr r) → t.mem = s.mem → t.sp = s.sp → t.lr = s.lr →
      t.rd = s.rd → t.wr = s.wr → WP isa (.block rest) t Q) →
    WP isa (.block (L.map (fun p => Instr.load .d p.1 b p.2) ++ rest)) s Q
  | [], s, rest, Q, _, _, _, k => k s (by simp) (fun _ _ => rfl) rfl rfl rfl rfl rfl
  | p :: L, s, rest, Q, hb, hok, hnd, k => by
    obtain ⟨o0, o1, o2, o3⟩ := hok p List.mem_cons_self
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_map] at hnd ⊢
    refine WP.cons (s' := s.write p.1 (s.mem.readW (B + BitVec.ofNat 64 p.2) 64)) ?_ ?_
    · rw [exec_load_d hb0 ⟨o1, by omega⟩ (by rw [hb]; exact o3), hb]
    refine loads_ok (B := B) hb0 L _ rest Q (by simp [State.write, Ne.symm o0, hb]) (fun q hq => ?_) hnd.2
      fun t g o m sp lr rd wr => ?_
    · obtain ⟨q0, q1, q2, q3⟩ := hok q (List.mem_cons_of_mem _ hq)
      exact ⟨q0, q1, q2, q3⟩
    refine k t (fun q hq => ?_) (fun r hr => ?_) m sp lr rd wr
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o _ (fun h => hnd.1 (by obtain ⟨q', hq', e⟩ := List.mem_map.mp h; exact ⟨q', hq', e⟩))]
        simp [State.write]
      · rw [g q hq]; rfl
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o r hr.2]; simp [State.write, hr.1]

/-- `entry`'s stores: distinct aligned offsets in the header. -/
theorem entryStores_ok : ∀ p ∈ entryStores, p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧ p.2 + 8 ≤ hEnd := by decide

theorem entryStores_nodup : (entryStores.map Prod.snd).Nodup := by decide

theorem entrySaved_mem : ∀ i < 19, (saved.getD i .r14, fSave + 8 * i) ∈ entryStores := by decide

/-- `addSp r off; ld r, 0(r)`: the stack argument `i` into `r`. -/
theorem argLoad_ok {STK : Nat} {σ s : State} (pre : CIn STK σ) (sp : s.sp = σ.sp) (rd : s.rd = σ.rd)
    {r : Reg} (hr : r ≠ .r0) {i : Nat} (hi : i < 4) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' r (stackArg s i) → s'.sp = s.sp → s'.lr = s.lr → WP isa (.block rest) s' Q) :
    WP isa (.block (.addSp r (96 + 8 * i) :: .load .d r r 0 :: rest)) s Q := by
  have ea : s.sp + BitVec.ofNat 64 (96 + 8 * i) = stackArgAddr s i := by
    simp only [stackArgAddr]; congr 2; omega
  have hin : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := by
    refine ⟨(mkG σ).rArgs, List.mem_append_left _ (by rw [rd, pre.rd]; simp), ?_⟩
    show Region.Contains ⟨σ.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 32⟩ _ _
    rw [show stackArgAddr s i = σ.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)) + BitVec.ofNat 64 (8 * i) by
      rw [stackArgAddr, sp, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.cons (exec_addSp (by omega)) ?_
  refine WP.cons (s' := s.write r (stackArg s i)) ?_ (k _ ⟨by simp [State.write], fun r' h => by simp [State.write, h],
    rfl, rfl, rfl⟩ rfl rfl)
  have ea' : (s.write r (s.sp + BitVec.ofNat 64 (96 + 8 * i))).gpr r + BitVec.ofNat 64 0 = stackArgAddr s i := by
    simp only [State.write, ite_true, BitVec.add_zero, ea]
  rw [exec_load_d hr ⟨by decide, by decide⟩ (by rw [ea']; exact hin), ea', write_write]
  rfl

/-- A run keeps the stack pointer. -/
theorem WP.sp_eq {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s fun t => t.sp = s.sp → Q t) :
    WP isa c s Q := by
  obtain ⟨tr, s', he, hq⟩ := h; exact ⟨tr, s', he, hq (Exec.sp he)⟩

theorem entrySaved_ne : ∀ i < 19, saved.getD i .r14 ∉ [Reg.r0, .r4, .r6, .r11, .r12] := by decide

/-- The words `entry` sets: the witnesses read and the status, both 0. -/
abbrev entryLS : List Nat := [fUsed, fStatus]

/-- `entry`: a state of the search. -/
theorem entry_ok {STK : Nat} {σ : State} (pre : CIn STK σ) :
    WP isa (.block entry) σ fun t => GI (mkG σ) STK σ (fun _ => 0) entryLS t ∧ t.gpr .r5 = σ.gpr .r5 := by
  have big : 8 * (64 * (mkG σ).pLen + 1024) ≤ (mkG σ).scrLen * 8 := by
    have := pre.scrLen; simp only [Spec.Dsa.generationScratchWords] at this
    show 8 * (64 * (σ.gpr .r5).toNat + 1024) ≤ (stackArg σ 3).toNat * 8; omega
  have fit : (mkG σ).scr.toNat + (mkG σ).scrLen * 8 ≤ 2 ^ 64 := pre.nC
  have hE : hEnd ≤ (mkG σ).scrLen * 8 := by simp only [hEnd, fSave]; omega
  refine WP.sp_eq ?_
  simp only [entry, List.cons_append]
  refine argLoad_ok (r := .r11) (i := 2) pre rfl rfl (by decide) (by decide) fun s₁ u₁ sp₁ lr₁ => ?_
  refine argLoad_ok (r := .r12) (i := 0) pre sp₁ (u₁.rd) (by decide) (by decide) fun s₂ u₂ sp₂ lr₂ => ?_
  refine argLoad_ok (r := .r4) (i := 1) pre (sp₂.trans sp₁) (u₂.rd.trans u₁.rd) (by decide) (by decide)
    fun s₃ u₃ sp₃ lr₃ => ?_
  refine WP.cons exec_mflr ?_
  refine wp_li (d := .r6) (imm := 0) (by decide) fun s₄ u₄ => ?_
  have sa : ∀ {x : State}, x.sp = σ.sp → x.mem = σ.mem → ∀ i, stackArg x i = stackArg σ i := fun hsp hm i => by
    simp only [stackArg, stackArgAddr, hsp, hm]
  have g4 : ∀ r, r ∉ [Reg.r0, .r4, .r6, .r11, .r12] → s₄.gpr r = σ.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.2.1]
    simp only [State.write, hr.1, ite_false]
    rw [u₃.other _ hr.2.1, u₂.other _ hr.2.2.2.2, u₁.other _ hr.2.2.2.1]
  have v11 : s₄.gpr .r11 = (mkG σ).scr := by
    rw [u₄.other _ (by decide)]; simp only [State.write]
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sa rfl rfl]; rfl
  have v12 : s₄.gpr .r12 = (mkG σ).wit := by
    rw [u₄.other _ (by decide)]; simp only [State.write]
    rw [u₃.other _ (by decide), u₂.gpr, sa sp₁ u₁.mem]; rfl
  have v4 : s₄.gpr .r4 = BitVec.ofNat 64 (mkG σ).witLen := by
    rw [u₄.other _ (by decide)]; simp only [State.write]
    rw [u₃.gpr, sa (sp₂.trans sp₁) (u₂.mem.trans u₁.mem)]; simp [mkG]
  have v0 : s₄.gpr .r0 = σ.lr := by
    rw [u₄.other _ (by decide)]; simp only [State.write, ite_true]; rw [lr₃, lr₂, lr₁]
  have v6 : s₄.gpr .r6 = 0 := by rw [u₄.gpr]; rfl
  have m₄ : s₄.mem = σ.mem := by rw [u₄.mem]; simp only [State.write]; rw [u₃.mem, u₂.mem, u₁.mem]
  have wr₄ : s₄.wr = σ.wr := by rw [u₄.wr]; simp only [State.write]; rw [u₃.wr, u₂.wr, u₁.wr]
  have rd₄ : s₄.rd = σ.rd := by rw [u₄.rd]; simp only [State.write]; rw [u₃.rd, u₂.rd, u₁.rd]
  have hw : ∀ p ∈ entryStores, p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧
      InRegions s₄.wr ((mkG σ).scr + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    obtain ⟨a, b, c⟩ := entryStores_ok p hp
    refine ⟨a, b, (mkG σ).rScr, by rw [wr₄, pre.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine stores_ok entryStores s₄ _ _ v11 hw entryStores_nodup fun t g _ _ rd wr rv f => ?_
  refine wp_addi (d := .r28) (n := .r11) (imm := 0) (by decide) (by decide) fun s₅ u₅ => WP.block_nil
    fun sp₅ => ⟨?_, ?_⟩
  · have val : ∀ {r : Reg} {o : Nat}, (r, o) ∈ entryStores → fw s₅.mem (mkG σ) o = s₄.gpr r := fun {r o} hp =>
      (congrArg (fun m : Mem => m.readW ((mkG σ).scr + BitVec.ofNat 64 o) 64) u₅.mem).trans (rv (r, o) hp)
    refine ⟨pre, rfl, sp₅, by rw [u₅.rd, rd, rd₄], by rw [u₅.wr, wr, wr₄], by rw [u₅.gpr, g, v11, BitVec.add_zero],
      fun i hi => by rw [val (entrySaved_mem i hi), g4 _ (entrySaved_ne i hi)], by rw [val (r := .r0) (o := fLR) (by decide), v0],
      fun p hp => ?_, fun o ho => ?_, fun o ho => ?_, ?_⟩
    · simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · rw [val (r := .r3) (o := fOut) (by decide), g4 _ (by decide)]; rfl
      · rw [val (r := .r12) (o := fWit) (by decide), v12]
      · rw [val (r := .r4) (o := fWitLen) (by decide), v4]
      · rw [val (r := .r9) (o := fHs) (by decide), g4 _ (by decide)]; rfl
      · rw [val (r := .r10) (o := fHsLen) (by decide), g4 _ (by decide)]; simp [mkG]
    · simp only [entryLS, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · rw [val (r := .r6) (o := fUsed) (by decide), v6]
      · rw [val (r := .r6) (o := fStatus) (by decide), v6]
    · simp only [entryLS, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> refine ⟨by decide, by decide, by decide, fun p hp => ?_⟩ <;>
        (simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide))
    · rw [u₅.mem, ← m₄]
      refine f.sub fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, c⟩ := entryStores_ok p hp
      exact ⟨(mkG σ).rScr, List.mem_cons_self, sw (mkG σ) (by omega)⟩
  · rw [u₅.other _ (by decide), g, g4 _ (by decide)]

end VG.Proof.Dsa.PPC64LE.Gen
