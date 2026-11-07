module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter search on RISC-V: entry and exit

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Entry.lean`). `entry_ok`: from the
contract's precondition, `entry` saves our caller's callee-saved registers
and our return address in `scratch`'s header, with the arguments, the seeds
left and 0 for the octets consumed: a state of the search (`GI`).
`restore_ok`: from a state of the search, `restore` gives back our caller's
registers and return address (`abiPreserved`). Both rest on `stores_ok` and
`loads_ok`, a list of stores or loads through a base register.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- A list of stores of registers through `b`, at distinct aligned offsets. -/
theorem stores_ok {B : Addr} {b : Reg} : ∀ (L : List (Reg × Nat)) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr b = B → (∀ p ∈ L, p.2 < 2048 ∧ (B + BitVec.ofNat 64 p.2).toNat % 8 = 0 ∧
      InRegions s.wr (B + BitVec.ofNat 64 p.2) 8) →
    (L.map Prod.snd).Nodup →
    (∀ t, t.gpr = s.gpr → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      (∀ p ∈ L, t.mem.readW (B + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) →
      Frame (L.map fun p => ⟨B + BitVec.ofNat 64 p.2, 8⟩) s.mem t.mem → WP isa (.block rest) t Q) →
    WP isa (.block (L.map (fun p => Instr.store .d p.1 b p.2) ++ rest)) s Q
  | [], s, rest, Q, _, _, _, k => k s rfl rfl rfl rfl (by simp) (Frame.refl _ _)
  | p :: L, s, rest, Q, hb, hok, hnd, k => by
    obtain ⟨o1, o2, o3⟩ := hok p List.mem_cons_self
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_map] at hnd ⊢
    refine wp_sd o1 (by rw [hb]) o2 o3 fun s₁ m₁ => ?_
    refine stores_ok L s₁ rest Q (by rw [m₁.gpr, hb]) (fun q hq => ?_) hnd.2 fun t g sp rd wr rv f => ?_
    · obtain ⟨q1, q2, q3⟩ := hok q (List.mem_cons_of_mem _ hq)
      exact ⟨q1, q2, by rw [m₁.wr]; exact q3⟩
    refine k t (g.trans m₁.gpr) (sp.trans m₁.sp) (rd.trans m₁.rd) (wr.trans m₁.wr) (fun q hq => ?_) ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [f.readW (r := ⟨B + BitVec.ofNat 64 q.2, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide),
          m₁.mem, Mem.readW_writeW_self64]
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
        have ne : q'.2 ≠ q.2 := fun e => hnd.1 ⟨q', hq', e⟩
        obtain ⟨a1, _, _⟩ := hok q' (List.mem_cons_of_mem _ hq')
        exact Offset.disjoint _ (by
          have := (hok q List.mem_cons_self).2.1; have := (hok q' (List.mem_cons_of_mem _ hq')).2.1
          have e1 : (B + BitVec.ofNat 64 q.2).toNat % 8 = (B.toNat + q.2) % 8 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q.2) (by omega)]; omega
          have e2 : (B + BitVec.ofNat 64 q'.2).toNat % 8 = (B.toNat + q'.2) % 8 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := q'.2) (by omega)]; omega
          omega) (by omega) (by omega)
      · rw [rv q hq, m₁.gpr]
    · rw [m₁.mem] at f
      have f1 : Frame (⟨B + BitVec.ofNat 64 p.2, 8⟩ :: L.map fun q => ⟨B + BitVec.ofNat 64 q.2, 8⟩) s.mem
          (s.mem.writeW (B + BitVec.ofNat 64 p.2) (s.gpr p.1)) :=
        (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      exact f1.trans (f.mono fun r hr => List.mem_cons_of_mem _ hr)

/-- A list of loads of distinct registers other than `b` through `b`. -/
theorem loads_ok {B : Addr} {b : Reg} :
    ∀ (L : List (Reg × Nat)) (s : State) (rest : List Instr) (Q : State → Prop),
    s.gpr b = B → (∀ p ∈ L, p.1 ≠ b ∧ p.2 < 2048 ∧ (B + BitVec.ofNat 64 p.2).toNat % 8 = 0 ∧
      InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 p.2) 8) →
    (L.map Prod.fst).Nodup →
    (∀ t, (∀ p ∈ L, t.gpr p.1 = s.mem.readW (B + BitVec.ofNat 64 p.2) 64) →
      (∀ r, r ∉ L.map Prod.fst → t.gpr r = s.gpr r) → t.mem = s.mem → t.sp = s.sp →
      t.rd = s.rd → t.wr = s.wr → WP isa (.block rest) t Q) →
    WP isa (.block (L.map (fun p => Instr.load .d p.1 b p.2) ++ rest)) s Q
  | [], s, rest, Q, _, _, _, k => k s (by simp) (fun _ _ => rfl) rfl rfl rfl rfl
  | p :: L, s, rest, Q, hb, hok, hnd, k => by
    obtain ⟨o0, o1, o2, o3⟩ := hok p List.mem_cons_self
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_map] at hnd ⊢
    refine wp_ld o1 (by rw [hb]) o2 o3 fun s₁ u₁ => ?_
    refine loads_ok (B := B) L s₁ rest Q (by rw [u₁.other _ (Ne.symm o0), hb]) (fun q hq => ?_) hnd.2
      fun t g o m sp rd wr => ?_
    · obtain ⟨q0, q1, q2, q3⟩ := hok q (List.mem_cons_of_mem _ hq)
      exact ⟨q0, q1, q2, by rw [u₁.rd, u₁.wr]; exact q3⟩
    refine k t (fun q hq => ?_) (fun r hr => ?_) (m.trans u₁.mem) (sp.trans u₁.sp) (rd.trans u₁.rd)
      (wr.trans u₁.wr)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o _ (fun h => hnd.1 (by obtain ⟨q', hq', e⟩ := List.mem_map.mp h; exact ⟨q', hq', e⟩)), u₁.gpr]
      · rw [g q hq, u₁.mem]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o r hr.2, u₁.other _ hr.1]

/-- `entry`'s stores: distinct aligned offsets in the header. -/
theorem entryStores_ok : ∀ p ∈ entryStores, p.2 < 2048 ∧ p.2 % 8 = 0 ∧ p.2 + 8 ≤ hEnd := by decide

theorem entryStores_nodup : (entryStores.map Prod.snd).Nodup := by decide

theorem entrySaved_mem : ∀ i < 12, (saved.getD i .s0, fSave + 8 * i) ∈ entryStores := by decide

theorem entrySaved_ne : ∀ i < 12, saved.getD i .s0 ∉ [Reg.t2, .t3] := by decide

/-- The words `entry` sets: the seeds left and the octets consumed. -/
abbrev entryLS : List Nat := [fLeft, fUsed]

/-- Their values. -/
abbrev eV (G : GP) : Nat → BitVec 64 := fun o => if o = fLeft then BitVec.ofNat 64 G.left else 0

theorem al_add {B : Addr} {o Z : Nat} (hB : B.toNat % 8 = 0) (ho : o % 8 = 0) (hf : B.toNat + Z ≤ 2 ^ 64)
    (hoZ : o + 8 ≤ Z) : (B + BitVec.ofNat 64 o).toNat % 8 = 0 := by
  have e : (B + BitVec.ofNat 64 o).toNat = B.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]; omega

/-- `entry`: a state of the search. -/
theorem entry_ok {STK : Nat} {σ : State} (pre : CIn STK σ) :
    WP isa (.block entry) σ fun t => GI (mkG σ) STK σ (eV (mkG σ)) entryLS t := by
  have big : 8 * (64 * (mkG σ).pLen + 1024) ≤ (mkG σ).scrLen * 8 := by
    have := pre.scrLen; simp only [Spec.Dsa.generationScratchWords] at this; omega
  have fit : (mkG σ).scr.toNat + (mkG σ).scrLen * 8 ≤ 2 ^ 64 := pre.nC
  have hE : hEnd ≤ (mkG σ).scrLen * 8 := by simp only [hEnd, fSave]; omega
  refine WP.sp_eq ?_
  simp only [entry, List.cons_append, List.append_assoc]
  have hin7 : InRegions (σ.rd ++ σ.wr) (σ.gpr .a7 + BitVec.ofNat 64 0) 8 := by
    refine ⟨(mkG σ).rState, List.mem_append_right _ (by rw [pre.wr]; simp), ?_⟩
    rw [BitVec.add_zero]; show Region.Contains ⟨σ.gpr .a7, 32⟩ (σ.gpr .a7) 8; simp [Region.Contains]
  refine wp_ld (by decide) rfl (by rw [BitVec.add_zero]; exact pre.alT) hin7 fun s₁ u₁ => ?_
  refine wp_li (d := .t3) (imm := 0) (by decide) fun s₂ u₂ => ?_
  have g2 : ∀ r, r ∉ [Reg.t2, .t3] → s₂.gpr r = σ.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.other _ hr.2, u₁.other _ hr.1]
  have m₂ : s₂.mem = σ.mem := by rw [u₂.mem, u₁.mem]
  have wr₂ : s₂.wr = σ.wr := by rw [u₂.wr, u₁.wr]
  have rd₂ : s₂.rd = σ.rd := by rw [u₂.rd, u₁.rd]
  have sp₂ : s₂.sp = σ.sp := by rw [u₂.sp, u₁.sp]
  have v5 : s₂.gpr .a5 = (mkG σ).scr := g2 _ (by decide)
  have vt2 : s₂.gpr .t2 = BitVec.ofNat 64 (mkG σ).left := by
    rw [u₂.other _ (by decide), u₁.gpr, BitVec.add_zero]; simp [mkG]
  have vt3 : s₂.gpr .t3 = 0 := by rw [u₂.gpr]; rfl
  have hw : ∀ p ∈ entryStores, p.2 < 2048 ∧ ((mkG σ).scr + BitVec.ofNat 64 p.2).toNat % 8 = 0 ∧
      InRegions s₂.wr ((mkG σ).scr + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    obtain ⟨a, b, c⟩ := entryStores_ok p hp
    refine ⟨a, al_add pre.alC b fit (by omega), (mkG σ).rScr, by rw [wr₂, pre.wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  refine stores_ok entryStores s₂ _ _ v5 hw entryStores_nodup fun t g _ rd wr rv f => ?_
  refine wp_mv (d := .s6) (n := .a5) fun s₅ u₅ => WP.block_nil fun sp₅ => ?_
  have val : ∀ {r : Reg} {o : Nat}, (r, o) ∈ entryStores → fw s₅.mem (mkG σ) o = s₂.gpr r := fun {r o} hp =>
    (congrArg (fun m : Mem => m.readW ((mkG σ).scr + BitVec.ofNat 64 o) 64) u₅.mem).trans (rv (r, o) hp)
  refine ⟨pre, rfl, sp₅, by rw [u₅.rd, rd, rd₂], by rw [u₅.wr, wr, wr₂], by rw [u₅.gpr, g, v5],
    fun i hi => by rw [val (entrySaved_mem i hi), g2 _ (entrySaved_ne i hi)],
    by rw [val (r := .ra) (o := fRA) (by decide), g2 _ (by decide)],
    fun p hp => ?_, fun o ho => ?_, fun o ho => ?_, ?_⟩
  · simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [val (r := .a0) (o := fOut) (by decide), g2 _ (by decide)]; rfl
    · rw [val (r := .a3) (o := fWit) (by decide), g2 _ (by decide)]; rfl
    · rw [val (r := .a4) (o := fWitLen) (by decide), g2 _ (by decide)]; simp [mkG]
    · rw [val (r := .a2) (o := fUsedArg) (by decide), g2 _ (by decide)]; rfl
    · rw [val (r := .a7) (o := fState) (by decide), g2 _ (by decide)]; rfl
    · rw [val (r := .a6) (o := fScrLen) (by decide), g2 _ (by decide)]; simp [mkG]
  · simp only [entryLS, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · rw [val (r := .t2) (o := fLeft) (by decide), vt2]; simp [eV]
    · rw [val (r := .t3) (o := fUsed) (by decide), vt3]; simp [eV, fUsed, fLeft]
  · simp only [entryLS, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> refine ⟨by decide, by decide, by decide, fun p hp => ?_⟩ <;>
      (simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
       rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide))
  · rw [u₅.mem, ← m₂]
    refine f.sub fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, c⟩ := entryStores_ok p hp
    exact ⟨(mkG σ).rScr, List.mem_cons_self, sw (mkG σ) (by omega)⟩

theorem restoreLoads_ok : ∀ p ∈ restoreLoads, p.1 ≠ .s6 ∧ p.2 < 2048 ∧ p.2 % 8 = 0 ∧ p.2 + 8 ≤ hEnd := by decide

theorem restoreLoads_nodup : (restoreLoads.map Prod.fst).Nodup := by decide

theorem restoreLoads_mem : ∀ i < 11, (saved.getD i .s0, fSave + 8 * i) ∈ restoreLoads := by decide

theorem preserved_cases : ∀ r ∈ preserved, r = .s6 ∨ ∃ i < 11, saved.getD i .s0 = r := by decide

/-- `restore`, from a state whose header holds our caller's registers and
return address: those back. -/
theorem restore_ok' {G : GP} {σ s : State} (h6 : s.gpr .s6 = G.scr) (hal : G.scr.toNat % 8 = 0)
    (hfit : G.scr.toNat + hEnd ≤ 2 ^ 64)
    (hsaved : ∀ i < 12, fw s.mem G (fSave + 8 * i) = σ.gpr (saved.getD i .s0)) (hra : fw s.mem G fRA = σ.gpr .ra)
    (hsp : s.sp = σ.sp) (hin : ∀ o, o + 8 ≤ hEnd → InRegions (s.rd ++ s.wr) (G.sa o) 8) :
    WP isa (.block restore) s fun t => abiPreserved σ t ∧ t.mem = s.mem ∧ t.gpr .a0 = s.gpr .a0 := by
  refine WP.sp_eq ?_
  simp only [restore]
  refine loads_ok (B := G.scr) (b := .s6) restoreLoads _ _ _ h6 (fun p hp => ?_) restoreLoads_nodup
    fun t v o m sp rd wr => ?_
  · obtain ⟨a, b, c, d⟩ := restoreLoads_ok p hp
    exact ⟨a, b, al_add hal c hfit d, hin _ d⟩
  have t6 : t.gpr .s6 = G.scr := by rw [o _ (by decide), h6]
  refine wp_ld (by decide) (by rw [t6]) (al_add hal (by decide) hfit (by decide))
    (by rw [rd, wr]; exact hin _ (by decide)) fun t' u => WP.block_nil fun sp' => ?_
  refine ⟨⟨fun r hr => ?_, by rw [sp', hsp], ?_⟩, by rw [u.mem, m], ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [u.gpr, m]; exact hsaved 11 (by decide)
    · have ne : saved.getD i .s0 ≠ .s6 := (restoreLoads_ok _ (restoreLoads_mem i hi)).1
      rw [u.other _ ne, v _ (restoreLoads_mem i hi)]; exact hsaved i (by omega)
  · rw [u.other _ (by decide), v (.ra, fRA) (by decide)]; exact hra
  · rw [u.other _ (by decide), o _ (by decide)]

/-- `restore`: our caller's registers and return address back. -/
theorem restore_ok {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}
    (h : GI G STK σ V LS s) :
    WP isa (.block restore) s fun t => abiPreserved σ t ∧ t.mem = s.mem ∧ t.gpr .a0 = s.gpr .a0 :=
  restore_ok' h.s6 h.scrAl (by have := h.scrFit; have := h.hEnd_le; omega) h.saved h.ra h.sp
    fun o ho => h.inRdWr (by have := h.hEnd_le; omega)

end VG.Proof.Dsa.RISCV64.PSearch
