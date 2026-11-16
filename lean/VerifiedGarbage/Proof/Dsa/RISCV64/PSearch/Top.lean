module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Pre
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-! # DSA parameter search on RISC-V: one width's search

`search_vp`: from the state `entry` leaves, the padding of the hash block
(`pre_vp`), then the controller's loop (`loop_vp`) to the end of its last
iteration.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch

section
variable {G : GP} {X : State → Prop}

/-- The padding of the hash block, the claim every seed's hashes share. -/
abbrev padCl {B N L : Nat} (G : GP) (md : MdStream.Md B N L) : Claims := [(sMsg + G.qLen, padTail md G.qLen)]

theorem search_vp (g : Geo) {B N L : Nat} (md : MdStream.Md B N L) (hL : L = 8)
    (hlb : md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)])
    (hgq : g.qLen = G.qLen) (hq : G.qLen < 2048) (hatt : AttemptOk G (padCl G md) X g.attempt)
    (hl : G.left ≤ 4096) (hRL : G.randB.length = G.randLen) (hR64 : G.randLen < 2 ^ 64) :
    VP (fun σ s => GI G STK0 σ (eV G) entryLS s ∧ X σ) g.search (St G (midCfg G (padCl G md) (lastPos G)) X) := by
  simp only [Geo.search]
  rw [hgq]
  refine VP.seq (pre_vp md hL hlb) ((loop_vp g hgq hq hatt hl hRL hR64).mono (fun σ s ⟨h, x⟩ => ⟨?_, x⟩) fun _ _ h => h)
  exact h.mono' (by simp [ctlCfg, eV, fLeft, fUsed]) (by simp [ctlCfg])

/-- `state`'s word at `o`, apart from what the search writes, as on entry. -/
theorem GI.stateW {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat} (h : GI G STK σ V LS s) {o : Nat}
    (ho : o + 8 ≤ 32) : s.mem.readW (G.state + BitVec.ofNat 64 o) 64 = σ.mem.readW (G.state + BitVec.ofNat 64 o) 64 := by
  have fit := h.pre.nT
  have e : (mkG σ).state = G.state := by rw [h.hG]
  have hd : ∀ r ∈ [G.rScr, rBelow σ STK], (⟨G.state + BitVec.ofNat 64 o, 8⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have sub : Region.Sub ⟨G.state + BitVec.ofNat 64 o, 8⟩ G.rState := Offset.sub_base _ (by omega)
    rcases hr with rfl | rfl
    · have := h.pre.cT; rw [h.hG] at this; exact this.symm.sub_left sub
    · have := h.pre.bT; rw [h.hG] at this; exact this.symm.sub_left sub
  exact (h.frame.readW (Region.contains_self _ _) hd (by decide))

/-- The width, `state[1]`, as on entry. -/
theorem GI.pLenW {STK : Nat} {σ s : State} {V : Nat → BitVec 64} {LS : List Nat} (h : GI G STK σ V LS s) :
    s.mem.readW (G.state + 8) 64 = BitVec.ofNat 64 G.pLen := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, h.stateW (o := 8) (by decide), ← h.hG]
  simp [mkG]

theorem eval_eq (s : State) (a b : Reg) : isa.eval (.eq a b) s = some (s.gpr a == s.gpr b) := rfl

/-- The dispatch on `state[1]` to the width's search. -/
theorem dispatch_vp (g1 g2 g3 : Geo) {Q : State → State → Prop}
    (h1 : G.pLen = 128 → VP (fun σ s => GI G STK0 σ (eV G) entryLS s ∧ X σ) g1.generate Q)
    (h2 : G.pLen = 256 → VP (fun σ s => GI G STK0 σ (eV G) entryLS s ∧ X σ) g2.generate Q)
    (h3 : G.pLen = 384 → VP (fun σ s => GI G STK0 σ (eV G) entryLS s ∧ X σ) g3.generate Q) :
    VP (fun σ s => GI G STK0 σ (eV G) entryLS s ∧ X σ) (dispatch g1 g2 g3) Q := by
  let F := fun σ s => GI G STK0 σ (eV G) entryLS s ∧ X σ
  have pub : ∀ (P : State → State → Prop), (∀ σ s, P σ s → F σ s) → Pub G P := fun P hP σ s h =>
    ⟨(hP σ s h).1.s6, by rw [(hP σ s h).1.sp, ← (hP σ s h).1.hG]; rfl⟩
  have pL := fun σ s (h : F σ s) => h.1.lens
  simp only [dispatch]
  refine VP.seq (G := fun σ s => F σ s ∧ s.gpr .t3 = G.state) (VP.pub (pub F fun _ _ h => h) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t3 fState]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ =>
      h.ldV (by decide) (by decide) (h.fixedV (v := G.state) (by simp [fixedWords])) fun t u =>
        WP.block_nil ⟨⟨h.of_upd u (by decide), x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => F σ s ∧ s.gpr .t2 = BitVec.ofNat 64 G.pLen ∧ s.gpr .t3 = 128)
    (VP.pub (pub _ fun _ _ h => h.1) [.t3]
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .t3]) (.block [.load .d .t2 .t3 8, .li .t3 128]),
        by kernel_rfl⟩ (fun _ _ _ _ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨h, x⟩, t3⟩ => ?_) ?_
  · have fit := h.pre.nT
    have al := h.pre.alT
    have e' : G.state = σ.gpr .a7 := by rw [← h.hG]; rfl
    have hA : (G.state + BitVec.ofNat 64 8).toNat = (σ.gpr .a7).toNat + 8 := by
      rw [e', BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8) (by decide), Nat.mod_eq_of_lt (by omega)]
    have hin : InRegions (s.rd ++ s.wr) (s.gpr .t3 + BitVec.ofNat 64 8) 8 := by
      refine ⟨G.rState, List.mem_append_right _ (by rw [h.wr, h.pre.wr, h.hG]; simp), ?_⟩
      rw [t3]; exact Offset.contains_base _ (by decide) (by decide)
    have hal : (s.gpr .t3 + BitVec.ofNat 64 8).toNat % 8 = 0 := by rw [t3, hA]; omega
    refine VG.RISCV64.Steps.wp_ld (by decide) rfl hal hin fun s₁ u₁ => ?_
    refine VG.RISCV64.Steps.wp_li (d := .t3) (imm := 128) (by decide) fun s₂ u₂ => WP.block_nil ⟨⟨?_, x⟩, ?_, u₂.gpr⟩
    · exact (h.of_upd u₁ (by decide)).of_upd u₂ (by decide)
    · rw [u₂.other _ (by decide), u₁.gpr, t3]; exact h.pLenW
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    show some (s₁.gpr .t2 == s₁.gpr .t3) = some (s₂.gpr .t2 == s₂.gpr .t3)
    rw [h₁.2.1, h₁.2.2, h₂.2.1, h₂.2.2]) ?_ ?_
  · by_cases e : G.pLen = 128
    · exact (h1 e).mono (fun σ s h => h.1.1) fun _ _ h => h
    · exact VP.of_false fun σ s ⟨⟨hF, t2, t3⟩, ev⟩ => e (by
        have hl := hF.1.lens
        rw [eval_eq, t2, t3, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl,
          ofNat_beq (by omega) (by decide)] at ev
        simpa using ev)
  · refine VP.seq (G := fun σ s => F σ s ∧ s.gpr .t2 = BitVec.ofNat 64 G.pLen ∧ s.gpr .t3 = 256 ∧ G.pLen ≠ 128)
      (VP.pub (pub _ fun _ _ h => h.1.1) []
        ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [.li .t3 256]), by kernel_rfl⟩
        (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, t2, t3⟩, ev⟩ => ?_) ?_
    · refine VG.RISCV64.Steps.wp_li (d := .t3) (imm := 256) (by decide) fun s₁ u₁ =>
        WP.block_nil ⟨⟨h.of_upd u₁ (by decide), x⟩, by rw [u₁.other _ (by decide), t2], u₁.gpr, fun e => ?_⟩
      have hl := h.lens
      rw [eval_eq, t2, t3, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ofNat_beq (by omega) (by decide)] at ev
      simp [e] at ev
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_eq, eval_eq, h₁.2.1, h₁.2.2.1, h₂.2.1, h₂.2.2.1]) ?_ ?_
    · by_cases e : G.pLen = 256
      · exact (h2 e).mono (fun σ s h => h.1.1) fun _ _ h => h
      · exact VP.of_false fun σ s ⟨⟨hF, t2, t3, _⟩, ev⟩ => e (by
          have hl := hF.1.lens
          rw [eval_eq, t2, t3, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
            ofNat_beq (by omega) (by decide)] at ev
          simpa using ev)
    · by_cases e : G.pLen = 384
      · exact (h3 e).mono (fun σ s h => h.1.1) fun _ _ h => h
      · exact VP.of_false fun σ s ⟨⟨hF, t2, t3, n128⟩, ev⟩ => by
          have hl := hF.1.lens
          rw [eval_eq, t2, t3, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
            ofNat_beq (by omega) (by decide)] at ev
          simp only [Option.some.injEq, decide_eq_false_iff_not] at ev
          omega

/-- The call's entry, for the public parameters `G`. -/
abbrev AE (G : GP) (σ u : State) : Prop := u = σ ∧ CIn STK0 σ ∧ mkG σ = G

/-- After the entry. -/
abbrev E1 (G : GP) (σ s : State) : Prop := GI G STK0 σ (eV G) entryLS s ∧ True

theorem entry_vp : VP (AE G) (.block entry) (E1 G) := by
  refine VP.taint [.a5, .a7] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.a5, .a7]) (.block entry),
      by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨e₁, _, g₁⟩ ⟨e₂, _, g₂⟩ => by
        subst e₁ e₂; show (mkG s₁).sp = (mkG s₂).sp; rw [g₁, g₂])
    (fun σ₁ σ₂ s₁ s₂ ⟨e₁, _, g₁⟩ ⟨e₂, _, g₂⟩ r hr => by
      subst e₁ e₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show (mkG s₁).scr = (mkG s₂).scr; rw [g₁, g₂]
      · show (mkG s₁).state = (mkG s₂).state; rw [g₁, g₂]) fun σ u ⟨hu, pre, hG⟩ => ?_
  subst hu hG
  exact WP.mono (entry_ok pre) fun t h => ⟨h, trivial⟩

end

end VG.Proof.Dsa.RISCV64.PSearch
