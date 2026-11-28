module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsHeight
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `levels`, the whole function

The prologue (`pro_ok`), the heights (`heights_ok`) and the epilogue
(`restore_ok`), from the precondition of `levelsContract` to its
postcondition and the calling convention (`levels_wp`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Levels

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs saveRegs restoreRegs)
open VG.Impl.SlhDsa.X86_64.Tree
open VG.Proof.Sha3.X86_64 (Upd ea_at wp_mov wp_movm wp_store)

theorem wp_rangeMap {f : Nat → Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s → (∀ j < K, ∀ t, P j t → WP isa (.block [f j]) t (P (j + 1))) →
      WP isa (.block ((List.range K).map f)) s (P K)
  | 0, _, h0, _ => WP.block_nil h0
  | K + 1, _, h0, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact WP.block_append (WP.mono (wp_rangeMap K h0 fun j hj => hs j (by omega)) fun t ht => hs K (by omega) t ht)

theorem oSave4 (i : Nat) : Layout.oSave 4 i = 2912 + 8 * i := rfl

/-- After the prologue. -/
structure ProPost (s t : State) : Prop where
  bx : t.gpr .rbx = s.gpr .rdi
  r12 : t.gpr .r12 = s.gpr .rsi
  r13 : t.gpr .r13 = s.gpr .r8
  r14 : t.gpr .r14 = s.gpr .rcx
  r15 : t.gpr .r15 = s.gpr .rdx
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 4 i)) 64 = s.gpr (savedRegs.getD i .rbx)
  v0 : t.mem.readW (at' (s.gpr .rdi) (Layout.oVar 4 0)) 64 = s.gpr .r9
  frame : Frame [⟨at' (s.gpr .rdi) (Layout.oSave 4 0), 56⟩] s.mem t.mem

theorem pro_ok {s : State} (hw : (⟨s.gpr .rdi, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block pro) s (ProPost s) := by
  have hc : ∀ j < 7, Region.Contains ⟨at' (s.gpr .rdi) (Layout.oSave 4 0), 56⟩ (at' (s.gpr .rdi) (2912 + 8 * j)) 8 :=
    fun j hj => by
      rw [oSave4, show at' (s.gpr .rdi) (2912 + 8 * j) = at' (s.gpr .rdi) (2912 + 8 * 0) + BitVec.ofNat 64 (8 * j) by
        rw [at_add]]
      exact Offset.contains_base _ (by omega) (by omega)
  unfold pro
  refine WP.block_append (WP.mono (wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr .rdi) (Layout.oSave 4 i)) 64 = s.gpr (savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr .rdi) (Layout.oSave 4 0), 56⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_) fun t ht => ?_)
  · refine wp_store (a := at' (s.gpr .rdi) (Layout.oSave 4 j)) (by rw [ea_at, g]) (by
      rw [w, oSave4]; exact in_scr hw (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
    refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
    · rw [m']
      by_cases e : i = j
      · subst e; rw [Mem.readW_writeW_self64, g]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave4, oSave4]; omega) (by rw [oSave4]; omega)
          (by rw [oSave4]; omega)) (by decide), sv i (by omega)]
    · rw [m']
      exact f.writeW (List.mem_singleton_self _) _ (by rw [oSave4]; exact hc j (by omega))
  obtain ⟨g, r, w, sv, f⟩ := ht
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => wp_mov fun t₅ u₅ => ?_
  have hbx : t₅.gpr .rbx = s.gpr .rdi := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, g]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_store (a := at' (s.gpr .rdi) (Layout.oVar 4 0)) (by rw [var, ea_at, hbx]) (by
      rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w]; exact in_scr hw (by decide))
    fun t₆ g₆ m₆ r₆ w₆ => WP.block_nil ?_
  have hr9 : t₅.gpr .r9 = s.gpr .r9 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g]
  refine ⟨by rw [g₆, hbx], ?_, ?_, ?_, ?_, ?_, by rw [r₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, r],
    by rw [w₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w], fun i hi => ?_, ?_, ?_⟩
  · rw [g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), g]
  · rw [g₆, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [g₆, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g]
  · rw [m₆, Mem.readW_writeW_sep (Offset.sep _ (by rw [oSave4, show Layout.oVar 4 0 = 2960 from rfl]; omega)
      (by rw [oSave4]; omega) (by decide)) (by decide), hm₅, sv i hi]
  · rw [m₆, Mem.readW_writeW_self64, hr9]
  · rw [m₆, hm₅]
    exact f.writeW (List.mem_singleton_self _) _ (by
      rw [show Layout.oVar 4 0 = 2912 + 8 * 6 from rfl]; exact hc 6 (by decide))


/-- The epilogue: the callee-saved registers from frame 4. -/
theorem restore_ok {σ t : State} {S : Addr} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hsv : ∀ i < 6, t.mem.readW (at' S (Layout.oSave 4 i)) 64 = σ.gpr (savedRegs.getD i .rbx))
    (hsp : t.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.mxcsr = t.mxcsr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (restoreRegs 4)) t Q := by
  have hin : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ i < 6, InRegions (u.rd ++ u.wr) (at' S (Layout.oSave 4 i)) 8 :=
    fun u hr hw' i hi => by rw [hr, hw']; exact in_scr' hw (by rw [oSave4]; omega)
  refine WP.mono_mx rfl (Q := fun u => u.mxcsr = t.mxcsr → Q u) ?_ fun _ h hm => h hm
  rw [show restoreRegs 4 = [Instr.mov .r15 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 4 5))),
    .mov .r14 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 4 4))), .mov .r13 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 4 3))),
    .mov .r12 (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 4 2))), .mov .rbp (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 4 1))),
    .mov .rbx (.mem (Impl.Sha3.X86_64.at_ .rbx (Layout.oSave 4 0)))] from rfl]
  refine wp_movm (by rw [ea_at, hbx]) (hin t rfl rfl 5 (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (by rw [ea_at, u₁.other _ (by decide), hbx]) (hin _ u₁.rd u₁.wr 4 (by decide)) fun t₂ u₂ => ?_
  refine wp_movm (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_movm (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 2 (by decide)) fun t₄ u₄ => ?_
  refine wp_movm (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 1 (by decide)) fun t₅ u₅ => ?_
  refine wp_movm (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 0 (by decide))
    fun t₆ u₆ => WP.block_nil fun hmx => ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) hmx fun r hr => ?_
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hsv 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hsv 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hsv 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hsv 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hsv 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hsv 5 (by decide)

variable {p : Params}

theorem pro_nm : (pro).all (fun i => !loadsMxcsr i) = true := rfl

theorem nodesAt_congr {m m' : Mem} {a : Addr} {c : Nat}
    (h : ∀ i < c, bytesAt m (a + BitVec.ofNat 64 (i * p.n)) p.n = bytesAt m' (a + BitVec.ofNat 64 (i * p.n)) p.n) :
    nodesAt p m a c = nodesAt p m' a c := by
  simp only [nodesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `levels`, from its precondition: its postcondition and the calling convention. -/
theorem levels_wp (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {s : State}
    (hpre : (levelsContract p stack).pre s) :
    WP isa (levels ⟨p.n, p.len⟩ name T.code) s fun s' => abiPreserved s s' ∧ (levelsContract p stack).post s s' := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eT : Layout.oSigTmp = 31648 := rfl
  have eN : Layout.oN = 12640 := rfl
  have eR : Layout.oRoots = 29280 := rfl
  have eNS : Layout.nodeSlots = 520 := rfl
  have hv : ∀ i, Layout.oVar 4 i = 2960 + 8 * i := fun _ => rfl
  obtain ⟨hR, ⟨pk₀, a₀, hE₀⟩, hrsi, hh1, hzh, hcnt, hcN, hcR, h9, hv5, hv6, hv7, hv8⟩ := hpre
  generalize hSdef : s.gpr .rdi = S at hR hE₀ hrsi hcN hcR hv5 hv6 hv7 hv8
  generalize hhdef : heightsOf s = h at hR hh1 hzh hcnt
  obtain ⟨no, hno, hno'⟩ : ∃ no, s.gpr .rsi = at' S no ∧ (no = Layout.oN ∨ no = Layout.oRoots) := by
    rcases hrsi with h' | h'
    · exact ⟨_, h', .inl rfl⟩
    · exact ⟨_, h', .inr rfl⟩
  have hcap : no + (2 ^ h + 8) * p.n ≤ Layout.oSigTmp := by
    rcases hno' with rfl | rfl
    · have := hcN hno; rw [hcnt] at this; omega
    · have := hcR hno; rw [hcnt] at this; omega
  have hP3 : (2 ^ h + 3) * p.n ≤ (2 ^ h + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
  have hnoR : ∀ l ≤ (2 ^ h + 3) * p.n, Region.Sub ⟨at' S no, l⟩ ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩ ∨
      Region.Sub ⟨at' S no, l⟩ ⟨at' S Layout.oRoots, 1024⟩ := fun l hl => by
    rcases hno' with rfl | rfl
    · have := hcN hno; rw [hcnt] at this
      exact .inl (Offset.sub S (Nat.le_refl _) (by omega))
    · have := hcR hno; rw [hcnt] at this
      exact .inr (Offset.sub S (Nat.le_refl _) (by omega))
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr := by rw [hR.wr_eq]; simp [scratchLen]
  have hwA : (⟨s.gpr .r8, h * p.n⟩ : Region) ∈ s.wr := by rw [hR.wr_eq]; simp
  have hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64 := hR.scr_fit
  have hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := hR.stk_scr
  have ha : a₀.length = 16 := by rw [← hE₀.adrsA 0 (by decide)]; simp [bytesAt]
  -- what the prologue writes
  have hdpro : ∀ X : Region, X.Disjoint ⟨S, Layout.oSigTmp⟩ → X.Disjoint ⟨at' S (Layout.oSave 4 0), 56⟩ :=
    fun X hX => disj_low hX (by rw [oSave4]; omega)
  have hlow : ∀ o l, o + l ≤ 2912 ∨ 2968 ≤ o → o + l ≤ 2 ^ 16 →
      Region.Disjoint ⟨at' S o, l⟩ ⟨at' S (Layout.oSave 4 0), 56⟩ := fun o l h₁ h₂ =>
    disj_scr S (by rw [oSave4]; omega) h₂ (by rw [oSave4]; omega)
  unfold levels
  refine WP.seq (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using pro_nm) (pro_ok (by rw [hSdef]; exact hwS))
    fun t₀ hp mx₀ => ?_)
  have hpf : Frame [⟨at' S (Layout.oSave 4 0), 56⟩] s.mem t₀.mem := by have := hp.frame; rwa [hSdef] at this
  have hpsv : ∀ i < 6, t₀.mem.readW (at' S (Layout.oSave 4 i)) 64 = s.gpr (savedRegs.getD i .rbx) := by
    have := hp.saved; rwa [hSdef] at this
  have hpv0 : t₀.mem.readW (at' S (Layout.oVar 4 0)) 64 = s.gpr .r9 := by have := hp.v0; rwa [hSdef] at this
  have hpbx : t₀.gpr .rbx = S := by rw [hp.bx, hSdef]
  have hkeep₀ : ∀ o, (o + 8 ≤ 2912 ∨ 2968 ≤ o) → o + 8 ≤ 2 ^ 16 →
      t₀.mem.readW (at' S o) 64 = s.mem.readW (at' S o) 64 := fun o h₁ h₂ =>
    hpf.readW (r := ⟨at' S o, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hlow o 8 h₁ h₂) (by decide)
  have hbytes₀ : ∀ X : Region, X.Disjoint ⟨S, Layout.oSigTmp⟩ → X.len ≤ 2 ^ 64 →
      bytesAt t₀.mem X.base X.len = bytesAt s.mem X.base X.len := fun X hX hl =>
    bytesAt_congr fun i hi => hpf.bytes (R := X)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdpro X hX) hl hi
  have hE₁ : Env p t₀.mem S pk₀ a₀ := by
    have hb : ∀ o l, 3296 ≤ o → o + l ≤ 10480 → bytesAt t₀.mem (at' S o) l = bytesAt s.mem (at' S o) l :=
      fun o l h₁ h₂ => bytesAt_congr fun i hi => hpf.bytes (R := ⟨at' S o, l⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hlow o l (.inr (by omega)) (by omega))
        (show l ≤ 2 ^ 64 by omega) hi
    have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
    have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
    refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hE₀.rc r hr k hk]; exact hkeep₀ _ (.inl (by omega)) (by omega)
    · rw [← hE₀.seedA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE₀.seedB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
    · rw [← hE₀.adrsA k hk, hb _ _ (by rw [hLA]; omega) (by rw [hLA]; omega)]
    · rw [← hE₀.adrsB k hk, hb _ _ (by rw [hLB]; omega) (by rw [hLB]; omega)]
  have hvar : ∀ i, 5 ≤ i → i ≤ 8 → t₀.mem.readW (at' S (Layout.oVar 4 i)) 64 = varAt s.mem S 4 i := fun i h₁ h₂ =>
    hkeep₀ _ (.inr (by rw [hv]; omega)) (by rw [hv]; omega)
  have hAd : Region.Disjoint ⟨s.gpr .r8, h * p.n⟩ ⟨S, Layout.oSigTmp⟩ := hR.out_scr
  refine WP.seq (WP.mono (heights_ok T name hn hf hst hs63 (S := S) (AU := s.gpr .r8) (no := no) (h := h)
    (z₀ := (s.gpr .rcx).toNat) (V0 := s.gpr .r9) (V5 := varAt s.mem S 4 5) (V6 := varAt s.mem S 4 6)
    (V7 := varAt s.mem S 4 7) (V8 := varAt s.mem S 4 8) (pkSeed := pk₀) (a16 := a₀)
    hpbx (by rw [hp.r12, hno]) hp.r13 (by rw [hp.r14, ofNat_toNat64]) (by rw [hp.r15, ← hcnt, ofNat_toNat64])
    hh1 hzh (by rcases hno' with rfl | rfl <;> decide) hcap hnoR hpv0 (hvar 5 (by decide) (by decide))
    (hvar 6 (by decide) (by decide)) (hvar 7 (by decide) (by decide)) (hvar 8 (by decide) (by decide)) h9 hv5 hv6
    (by rw [hp.wr]; exact hwS) hS (by rw [hp.sp]; exact hstk) hE₁ ha (by rw [hp.wr]; exact hwA) hR.out_fit hAd
    (by rw [hp.sp]; exact hR.stk_out.symm)) fun t₁ hh => ?_)
  refine restore_ok (σ := s) (S := S) (by rw [hh.bx, hpbx]) (by rw [hh.wr, hp.wr]; exact hwS)
    (fun i hi => by rw [hh.vars _ (by rw [oSave4]; omega) (by rw [oSave4, hv]; omega), hpsv i hi])
    (by rw [hh.sp, hp.sp]) fun t₂ m₂ mx₂ cs₂ => ?_
  -- the frame of the whole function
  have hfr : Frame (levelsChanges p S (at' S no) (2 ^ h) ++ [⟨s.gpr .r8, h * p.n⟩, below (s.gpr .rsp) stack])
      s.mem t₂.mem := by
    have f := hh.frame
    rw [hp.sp] at f
    rw [m₂]
    refine (hpf.sub fun r hr => ?_).trans f
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨at' S (Layout.oFrame 4), 128⟩, by simp [levelsChanges],
      Offset.sub S (by rw [oSave4]; decide) (by rw [oSave4]; decide)⟩
  refine ⟨⟨cs₂, ?_, by rw [mx₂, hh.mx, mx₀]⟩, fun pkSeed a16 hE => ?_⟩
  · refine hfr.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · have hsc : Region.Sub ⟨S, Layout.oSigTmp⟩ ⟨S, scratchLen⟩ := by
        have hs := Offset.sub_base S (d := 0) (n := Layout.oSigTmp) (k := scratchLen) (by rw [eT]; decide)
        rwa [← scr0 S] at hs
      exact hR.ret_scr.sub_right fun x h' => hsc x (levelsChanges_low hn32 S hcap r hr x h')
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.ret_out
      · exact Offset.base_disjoint_below _ (by omega)
  -- the postcondition
  have hL : nodesAt p t₀.mem (at' S no) (2 ^ h) = nodesAt p s.mem (s.gpr .rsi) (s.gpr .rdx).toNat := by
    rw [hno, hcnt]
    refine nodesAt_congr fun i hi => ?_
    have hi' : (i + 1) * p.n ≤ (2 ^ h + 8) * p.n := Nat.mul_le_mul_right _ (by omega)
    rw [at_add]
    exact bytesAt_congr fun j hj => hpf.bytes (R := ⟨at' S (no + i * p.n), p.n⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hlow _ _ (.inr (by rcases hno' with rfl | rfl <;> omega)) (by rw [Nat.add_mul, Nat.one_mul] at hi'; omega))
      (show p.n ≤ 2 ^ 64 by omega) hj
  dsimp only [levelsContract]
  rw [hSdef] at hE
  rw [hSdef, hhdef]
  obtain rfl : pkSeed = pk₀ := by rw [← hE.seedA 0 (by decide), hE₀.seedA 0 (by decide)]
  obtain rfl : a16 = a₀ := by rw [← hE.adrsA 0 (by decide), hE₀.adrsA 0 (by decide)]
  refine ⟨by rw [m₂]; exact hh.env, by rw [m₂, hno, hh.root, hL, hno], fun r hr => ?_, by rw [hno, hcnt]; exact hfr⟩
  have hX : Region.Disjoint ⟨s.gpr .r8 + BitVec.ofNat 64 (r * p.n), p.n⟩ ⟨S, Layout.oSigTmp⟩ := by
    have : r * p.n + p.n ≤ h * p.n := by
      have := Nat.mul_le_mul_right p.n (show r + 1 ≤ h by omega); rwa [Nat.add_mul, Nat.one_mul] at this
    exact hAd.sub_left (Offset.sub_base _ this)
  rw [m₂, hh.auth r hr, hL, hbytes₀ _ hX (show p.n ≤ 2 ^ 64 by omega)]


end VG.Proof.SlhDsa.X86_64.Levels
