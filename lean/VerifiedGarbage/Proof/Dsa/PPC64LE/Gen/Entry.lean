module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: entry and exit

`entry_ok`: from the contract's precondition, `entry` saves our caller's
registers and our return address in `scratch`'s header, with `out`, `used`,
`rand` and its length, `state`, the seeds left from `state[0]`, and 0 for the
cursor and the status: a state of the search (`GI`), with the modulus's width
in `r12`. `restore_ok`: from a state of the search, `restore`
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

/-- A list of stores of registers through `r8`, at distinct aligned offsets. -/
theorem stores_ok {B : Addr} : ∀ (L : List (Reg × Nat)) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr .r8 = B → (∀ p ∈ L, p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧ InRegions s.wr (B + BitVec.ofNat 64 p.2) 8) →
    (L.map Prod.snd).Nodup →
    (∀ t, t.gpr = s.gpr → t.sp = s.sp → t.lr = s.lr → t.rd = s.rd → t.wr = s.wr →
      (∀ p ∈ L, t.mem.readW (B + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) →
      Frame (L.map fun p => ⟨B + BitVec.ofNat 64 p.2, 8⟩) s.mem t.mem → WP isa (.block rest) t Q) →
    WP isa (.block (L.map (fun p => Instr.store .d p.1 .r8 p.2) ++ rest)) s Q
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

theorem entrySaved_ne : ∀ i < 19, saved.getD i .r14 ∉ [Reg.r0, .r4, .r11, .r12] := by decide

/-- The words `entry` sets: the seeds left, the cursor and the status. -/
abbrev entryLS : List Nat := [fSeedLeft, fC, fStatus]

/-- Their values. -/
abbrev eV (G : GP) : Nat → BitVec 64 := fun o => if o = fSeedLeft then BitVec.ofNat 64 G.k0 else 0

/-- `entry`: a state of the search, with the modulus's width in `r12`. -/
theorem entry_ok {STK : Nat} {σ : State} (pre : CIn STK σ) :
    WP isa (.block entry) σ fun t =>
      GI (mkG σ) STK σ (eV (mkG σ)) entryLS t ∧ t.gpr .r12 = BitVec.ofNat 64 (mkG σ).pLen := by
  have big : 8 * (64 * (mkG σ).pLen + 1024) ≤ (mkG σ).scrLen * 8 := by
    have := pre.scrLen; simp only [Spec.Dsa.generationScratchWords] at this
    show 8 * (64 * pLenOf σ + 1024) ≤ (σ.gpr .r9).toNat * 8; omega
  have fit : (mkG σ).scr.toNat + (mkG σ).scrLen * 8 ≤ 2 ^ 64 := pre.nC
  have hE : hEnd ≤ (mkG σ).scrLen * 8 := by simp only [hEnd, fSave]; omega
  have inSt : ∀ o, o + 8 ≤ 32 → InRegions (σ.rd ++ σ.wr) (σ.gpr .r10 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨(mkG σ).rSt, List.mem_append_right _ (by rw [pre.wr]; simp), Offset.contains_base _ ho (by omega)⟩
  refine WP.sp_eq ?_
  simp only [entry, List.cons_append]
  refine WP.cons exec_mflr ?_
  have u₀ : Upd σ (σ.write .r0 σ.lr) .r0 σ.lr := Upd.write _ _ _
  refine wp_ld (t := .r11) (by decide) ⟨by decide, by decide⟩ (a := σ.gpr .r10 + BitVec.ofNat 64 0)
    (by rw [u₀.other _ (by decide)]) (by rw [u₀.rd, u₀.wr]; exact inSt 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (t := .r12) (by decide) ⟨by decide, by decide⟩ (a := σ.gpr .r10 + BitVec.ofNat 64 8)
    (by rw [u₁.other _ (by decide), u₀.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact inSt 8 (by decide)) fun s₂ u₂ => ?_
  refine wp_li (d := .r4) (imm := 0) (by decide) fun s₄ u₄ => ?_
  have g4 : ∀ r, r ∉ [Reg.r0, .r4, .r11, .r12] → s₄.gpr r = σ.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other _ hr.2.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.2.1, u₀.other _ hr.1]
  have m₄ : s₄.mem = σ.mem := by rw [u₄.mem, u₂.mem, u₁.mem, u₀.mem]
  have v8 : s₄.gpr .r8 = (mkG σ).scr := g4 _ (by decide)
  have v11 : s₄.gpr .r11 = BitVec.ofNat 64 (mkG σ).k0 := by
    rw [u₄.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₀.mem, BitVec.add_zero]
    simp [mkG]
  have v12 : s₄.gpr .r12 = BitVec.ofNat 64 (mkG σ).pLen := by
    rw [u₄.other _ (by decide), u₂.gpr, u₁.mem, u₀.mem]
    simp [mkG, pLenOf]
  have v0 : s₄.gpr .r0 = σ.lr := by
    rw [u₄.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₀.gpr]
  have v4 : s₄.gpr .r4 = 0 := by rw [u₄.gpr]; rfl
  have wr₄ : s₄.wr = σ.wr := by rw [u₄.wr, u₂.wr, u₁.wr, u₀.wr]
  have rd₄ : s₄.rd = σ.rd := by rw [u₄.rd, u₂.rd, u₁.rd, u₀.rd]
  have hw : ∀ p ∈ entryStores, p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧
      InRegions s₄.wr ((mkG σ).scr + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    obtain ⟨a, b, c⟩ := entryStores_ok p hp
    refine ⟨a, b, (mkG σ).rScr, by rw [wr₄, pre.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine stores_ok entryStores s₄ _ _ v8 hw entryStores_nodup fun t g _ _ rd wr rv f => ?_
  refine wp_addi (d := .r28) (n := .r8) (imm := 0) (by decide) (by decide) fun s₅ u₅ => WP.block_nil
    fun sp₅ => ⟨?_, ?_⟩
  · have val : ∀ {r : Reg} {o : Nat}, (r, o) ∈ entryStores → fw s₅.mem (mkG σ) o = s₄.gpr r := fun {r o} hp =>
      (congrArg (fun m : Mem => m.readW ((mkG σ).scr + BitVec.ofNat 64 o) 64) u₅.mem).trans (rv (r, o) hp)
    refine ⟨pre, rfl, sp₅, by rw [u₅.rd, rd, rd₄], by rw [u₅.wr, wr, wr₄], by rw [u₅.gpr, g, v8, BitVec.add_zero],
      fun i hi => by rw [val (entrySaved_mem i hi), g4 _ (entrySaved_ne i hi)],
      by rw [val (r := .r0) (o := fLR) (by decide), v0], fun p hp => ?_, fun o ho => ?_, fun o ho => ?_, ?_⟩
    · simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · rw [val (r := .r3) (o := fOut) (by decide), g4 _ (by decide)]; rfl
      · rw [val (r := .r6) (o := fWit) (by decide), g4 _ (by decide)]; rfl
      · rw [val (r := .r7) (o := fWitLen) (by decide), g4 _ (by decide)]; simp [mkG]
      · rw [val (r := .r5) (o := fUsedP) (by decide), g4 _ (by decide)]; rfl
      · rw [val (r := .r10) (o := fStP) (by decide), g4 _ (by decide)]; rfl
    · simp only [entryLS, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · rw [val (r := .r11) (o := fSeedLeft) (by decide), v11]; simp [eV]
      · rw [val (r := .r4) (o := fC) (by decide), v4]; rfl
      · rw [val (r := .r4) (o := fStatus) (by decide), v4]; rfl
    · simp only [entryLS, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl <;> refine ⟨by decide, by decide, by decide, fun p hp => ?_⟩ <;>
        (simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
         rcases hp with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide))
    · rw [u₅.mem, ← m₄]
      refine f.sub fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨_, _, c⟩ := entryStores_ok p hp
      exact ⟨(mkG σ).rScr, List.mem_cons_self, sw (mkG σ) (by omega)⟩
  · rw [u₅.other _ (by decide), g, v12]

theorem restoreLoads_ok : ∀ p ∈ restoreLoads, p.1 ≠ .r28 ∧ p.2 < 2 ^ 15 ∧ p.2 % 8 = 0 ∧ p.2 + 8 ≤ hEnd := by decide

theorem restoreLoads_nodup : (restoreLoads.map Prod.fst).Nodup := by decide

theorem restoreLoads_mem : ∀ i < 18, (saved.getD i .r14, fSave + 8 * i) ∈ restoreLoads := by decide

theorem preserved_cases : ∀ r ∈ preserved, r = .r28 ∨ ∃ i < 18, saved.getD i .r14 = r := by decide

/-- `restore`, from a state whose header holds our caller's registers and
return address: those back. -/
theorem restore_ok' {G : GP} {σ s : State} (h28 : s.gpr .r28 = G.scr)
    (hsaved : ∀ i < 19, fw s.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .r14)) (hlr : fw s.mem G fLR = σ.lr)
    (hsp : s.sp = σ.sp) (hin : ∀ o, o + 8 ≤ hEnd → InRegions (s.rd ++ s.wr) (G.sa o) 8) :
    WP isa (.block restore) s fun t => abiPreserved σ t ∧ t.mem = s.mem ∧ t.gpr .r3 = s.gpr .r3 := by
  refine WP.sp_eq ?_
  simp only [restore, List.cons_append, List.append_assoc]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [h28]) (hin fLR (by decide)) fun s₁ u₁' => ?_
  have u₁ : Upd s s₁ .r0 σ.lr := by rw [← hlr]; exact u₁'
  refine WP.cons exec_mtlr ?_
  have g₂ : ∀ r, ({ s₁ with lr := s₁.gpr .r0 } : State).gpr r = s₁.gpr r := fun _ => rfl
  refine loads_ok (B := G.scr) (b := .r28) (by decide) restoreLoads _ _ _
    (by rw [g₂, u₁.other _ (by decide), h28]) (fun p hp => ?_) restoreLoads_nodup
    fun t v o m _ lr rd wr => ?_
  · obtain ⟨a, b, c, d⟩ := restoreLoads_ok p hp
    refine ⟨a, b, c, ?_⟩
    show InRegions (s₁.rd ++ s₁.wr) _ 8
    rw [u₁.rd, u₁.wr]; exact hin _ d
  have t28 : t.gpr .r28 = G.scr := by rw [o _ (by decide), g₂, u₁.other _ (by decide), h28]
  have tm : t.mem = s.mem := by rw [m]; exact u₁.mem
  have ea : t.gpr .r28 + BitVec.ofNat 64 (fSave + 8 * 18) = G.sa (fSave + 8 * 18) := by rw [t28]
  have hin' : InRegions (t.rd ++ t.wr) (G.sa (fSave + 8 * 18)) 8 := by
    rw [rd, wr]; show InRegions (s₁.rd ++ s₁.wr) _ 8
    rw [u₁.rd, u₁.wr]; exact hin _ (by decide)
  refine WP.cons (s' := t.write .r28 (t.mem.readW (G.sa (fSave + 8 * 18)) 64)) ?_ (WP.block_nil fun sp' => ?_)
  · show exec (.load .d .r28 .r28 (fSave + 8 * 18)) t = _
    rw [exec_load_d (t := .r28) (n := .r28) (off := fSave + 8 * 18) (by decide) ⟨by decide, by decide⟩
      (by rw [ea]; exact hin'), ea]
  have v28 : t.mem.readW (G.sa (fSave + 8 * 18)) 64 = σ.gpr .r28 := by
    rw [tm]; exact hsaved 18 (by decide)
  have spT : (t.write .r28 (t.mem.readW (G.sa (fSave + 8 * 18)) 64)).sp = σ.sp := by rw [sp', hsp]
  refine ⟨⟨fun r hr => ?_, spT, ?_⟩, ?_, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · simp only [State.write, ite_true]; exact v28
    · have ne : saved.getD i .r14 ≠ .r28 := (restoreLoads_ok _ (restoreLoads_mem i hi)).1
      simp only [State.write, ne, ite_false]
      rw [v _ (restoreLoads_mem i hi)]
      show s₁.mem.readW _ 64 = _
      rw [u₁.mem]; exact hsaved i (by omega)
  · show t.lr = σ.lr
    rw [lr]; show s₁.gpr .r0 = σ.lr; rw [u₁.gpr]
  · show t.mem = s.mem; exact tm
  · show (t.write .r28 _).gpr .r3 = _
    simp only [State.write, show Reg.r3 ≠ .r28 by decide, ite_false]
    rw [o _ (by decide), g₂, u₁.other _ (by decide)]

/-- `restore`: our caller's registers and return address back. -/
theorem restore_ok {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}
    (h : GI G STK σ V LS s) :
    WP isa (.block restore) s fun t => abiPreserved σ t ∧ t.mem = s.mem ∧ t.gpr .r3 = s.gpr .r3 :=
  restore_ok' h.r28 h.saved h.lr h.sp fun o ho => h.inRdWr (by have := h.hEnd_le; omega)

end VG.Proof.Dsa.PPC64LE.Gen
