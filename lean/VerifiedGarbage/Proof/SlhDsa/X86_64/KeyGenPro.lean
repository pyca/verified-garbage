module

-- separate module: the prologue of key generation, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssCT
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Shake
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks

/-!
# SLH-DSA (SHAKE) on x86-64: the prologue of key generation

From `keygen(seeds = rdi, sk = rsi, pk = rdx, scratch = rcx)`'s entry to
its call of `xmssTree`: the callee-saved registers saved at `oKgSave`, the
table of round constants (`RcTable`), `SK.seed`, `SK.prf` and `PK.seed` at
`oKeys`, `PK.seed` and the address of the top layer's tree in every lane
(`Env`), and the arguments of the call.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.KeyGen

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs copyWords setField setFieldR)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave kgSave kgRestore rcTable seedLanes treeLanes writeKeys)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store wp_movi64 ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (in_scr in_scr' at_add disj_scr scr0)

theorem oKgSave_eq : oKgSave = 34080 := rfl

/-! ## The saved registers -/

/-- After `kgSave`. -/
structure SavePost (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr .rcx) (oKgSave + 8 * i)) 64 = s.gpr (savedRegs.getD i .rbx)
  frame : Frame [⟨at' (s.gpr .rcx) oKgSave, 48⟩] s.mem t.mem

theorem save_ok {s : State} (hw : (⟨s.gpr .rcx, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (kgSave .rcx)) s (SavePost s) := by
  have hc : ∀ j < 6, Region.Contains ⟨at' (s.gpr .rcx) oKgSave, 48⟩ (at' (s.gpr .rcx) (oKgSave + 8 * j)) 8 :=
    fun j hj => by
      rw [← at_add]
      exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr .rcx) (oKgSave + 8 * i)) 64 = s.gpr (savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr .rcx) oKgSave, 48⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_)
    fun t ⟨g, r, w, sv, f⟩ => ⟨g, r, w, sv, f⟩
  refine wp_store (a := at' (s.gpr .rcx) (oKgSave + 8 * j)) (by rw [ea_at, g]) (by
    rw [w, oKgSave_eq]; exact in_scr hw (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
  refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
  · rw [m']
    by_cases e : i = j
    · subst e; rw [Mem.readW_writeW_self64, g]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [oKgSave_eq]; omega) (by rw [oKgSave_eq]; omega)
        (by rw [oKgSave_eq]; omega)) (by decide), sv i (by omega)]
  · rw [m']
    exact f.writeW (List.mem_singleton_self _) _ (hc j (by omega))

/-- The blocks of a `flatMap` over `range K`, one invariant at each. -/
theorem wp_flatMap {f : Nat → List Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s → (∀ j < K, ∀ t, P j t → WP isa (.block (f j)) t (P (j + 1))) →
      WP isa (.block ((List.range K).flatMap f)) s (P K)
  | 0, _, h0, _ => WP.block_nil h0
  | K + 1, _, h0, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (wp_flatMap K h0 fun j hj => hs j (by omega)) fun t ht =>
      hs K (by omega) t ht)

/-! ## The round constants -/

/-- After `r` rows of `rcTable`. -/
def RcI (s : State) (S : Addr) (r : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r' < r, ∀ k < 4, t.mem.readW (S + BitVec.ofNat 64 (1600 + 32 * r' + 8 * k)) 64 = Spec.Sha3.RC r') ∧
    Frame [⟨at' S 1600, 768⟩] s.mem t.mem

theorem rc_ok {s : State} {S : Addr} (hb : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block rcTable) s (RcI s S 24) := by
  refine wp_flatMap (P := RcI s S) 24 ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    fun r hr t ⟨hg, rd, w, rc, f⟩ => ?_
  refine wp_movi64 fun t₁ u₁ => ?_
  refine WP.mono (Levels.wp_rangeMap (P := fun j u => (∀ g, g ≠ .rax → u.gpr g = s.gpr g) ∧ u.gpr .rax = Spec.Sha3.RC r ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r' < r, ∀ k < 4, u.mem.readW (S + BitVec.ofNat 64 (1600 + 32 * r' + 8 * k)) 64 = Spec.Sha3.RC r') ∧
      (∀ k < j, u.mem.readW (S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k)) 64 = Spec.Sha3.RC r) ∧
      Frame [⟨at' S 1600, 768⟩] s.mem u.mem) 4
    ⟨fun g h => by rw [u₁.other _ h, hg _ h], u₁.gpr, by rw [u₁.rd, rd], by rw [u₁.wr, w],
      fun r' h k hk => by rw [u₁.mem]; exact rc r' h k hk, fun _ h => absurd h (by omega), by rw [u₁.mem]; exact f⟩
    fun j hj u ⟨g', ax, rd', w', rc', cur, f'⟩ => ?_) fun u ⟨g', _, rd', w', rc', cur, f'⟩ => ?_
  · refine wp_store (a := S + BitVec.ofNat 64 (1600 + 32 * r + 8 * j)) (by rw [ea_at, g' _ (by decide), hb])
      (by rw [w']; exact in_scr hw (by omega)) fun u' gu mu ru wu => WP.block_nil ?_
    have hsep : ∀ {r' k : Nat}, r' ≤ r → k < 4 → (r' ≠ r ∨ k ≠ j) →
        Mem.Sep (S + BitVec.ofNat 64 (1600 + 32 * r' + 8 * k)) (64 / 8) (S + BitVec.ofNat 64 (1600 + 32 * r + 8 * j)) (64 / 8) :=
      fun h₁ h₂ h₃ => Offset.sep _ (by omega) (by omega) (by omega)
    refine ⟨fun g h => by rw [gu, g' _ h], by rw [gu, ax], by rw [ru, rd'], by rw [wu, w'],
      fun r' h k hk => ?_, fun k hk => ?_, ?_⟩
    · rw [mu, Mem.readW_writeW_sep (hsep (by omega) hk (.inl (by omega))) (by decide), rc' r' h k hk]
    · rw [mu]
      by_cases e : k = j
      · subst e; rw [Mem.readW_writeW_self64, ax]
      · rw [Mem.readW_writeW_sep (hsep (Nat.le_refl _) (by omega) (.inr e)) (by decide), cur k (by omega)]
    · rw [mu]
      refine f'.writeW (List.mem_singleton_self _) _ ?_
      rw [show S + BitVec.ofNat 64 (1600 + 32 * r + 8 * j) = at' S 1600 + BitVec.ofNat 64 (32 * r + 8 * j) by
        rw [at_add, Nat.add_assoc]]
      exact Offset.contains_base _ (by omega) (by omega)
  · refine ⟨g', rd', w', fun r' h k hk => ?_, f'⟩
    by_cases e : r' = r
    · subst e; exact cur k hk
    · exact rc' r' (by omega) k hk

/-! ## Copies -/

/-- `bytesAt` at two addresses of memories that agree there, byte for byte. -/
theorem bytesAt_eq_of {m m' : Mem} {a b : Addr} {L : Nat}
    (h : ∀ i < L, m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)) : bytesAt m a L = bytesAt m' b L := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `copyWords .rbx d₂ .rbx d₁ w` within `scratch`, in bytes. -/
theorem copyS_ok {s : State} {S : Addr} (hb : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    {d₁ d₂ w : Nat} (h₁ : d₁ + 8 * w ≤ 2 ^ 16) (h₂ : d₂ + 8 * w ≤ 2 ^ 16) (hd : d₁ + 8 * w ≤ d₂ ∨ d₂ + 8 * w ≤ d₁)
    {Q : State → Prop}
    (k : ∀ t, (∀ g, g ≠ .rax → t.gpr g = s.gpr g) → t.rd = s.rd → t.wr = s.wr →
      bytesAt t.mem (at' S d₂) (8 * w) = bytesAt s.mem (at' S d₁) (8 * w) →
      Frame [⟨at' S d₂, 8 * w⟩] s.mem t.mem → Q t) :
    WP isa (.block (copyWords .rbx d₂ .rbx d₁ w)) s Q := by
  refine WP.mono (Levels.copy_ok (S := S) (t := .rbx) (sr := .rbx) (by decide) (by decide) (a := 0) (b := 0)
    (d₁ := d₁) (d₂ := d₂) w s (by rw [hb]; exact scr0 S) (by rw [hb]; exact scr0 S) hw (by omega) (by omega)
    (by omega)) fun t ⟨g, r, w', c, f⟩ => k t g r w' ?_ (by simpa using f)
  refine bytesAt_eq_of fun i hi => ?_
  rw [at_add, at_add]
  simpa using c i hi

/-- The `n` bytes at `rdi + n·c` (`c < 3`: `SK.seed`, `SK.prf`, `PK.seed`)
copied to `oKeys + 32 c`. -/
def KeysI (n : Nat) (s : State) (S X : Addr) (c : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ c' < c, bytesAt t.mem (at' S (Layout.oKeys + 32 * c')) n = bytesAt s.mem (X + BitVec.ofNat 64 (n * c')) n) ∧
    Frame [⟨at' S Layout.oKeys, 96⟩] s.mem t.mem

theorem keys_ok {n : Nat} (hn : n ≤ 32) (h8 : n % 8 = 0) {s : State} {S X : Addr} (hb : s.gpr .rbx = S)
    (hx : s.gpr .rdi = X) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hr : (⟨X, 3 * n⟩ : Region) ∈ s.rd)
    (hXf : X.toNat + 3 * n ≤ 2 ^ 64) (hdis : Region.Disjoint ⟨X, 3 * n⟩ ⟨S, 2 ^ 16⟩) :
    WP isa (.block ((List.range 3).flatMap fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rdi (n * c) (n / 8))) s
      (KeysI n s S X 3) := by
  have eK : Layout.oKeys = 3168 := rfl
  have h8n : 8 * (n / 8) = n := by omega
  refine wp_flatMap (P := KeysI n s S X) 3 ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    fun c hc t ⟨hg, rd, w, kc, f⟩ => ?_
  have hbt : t.gpr .rbx = S := by rw [hg _ (by decide), hb]
  have hxt : t.gpr .rdi = X := by rw [hg _ (by decide), hx]
  -- the seeds are outside what the copies write
  have hX : ∀ {o l : Nat}, o + l ≤ 3 * n → Region.Disjoint ⟨X + BitVec.ofNat 64 o, l⟩ ⟨at' S Layout.oKeys, 96⟩ :=
    fun {o l} h => (hdis.sub_left (Offset.sub_base X (by omega))).sub_right (Offset.sub_base S (by rw [eK]; omega))
  refine WP.mono (copyWords_ok (s := t) (t := .rbx) (src := .rdi) (by decide) (by decide)
    (d₂ := Layout.oKeys + 32 * c) (d₁ := n * c) (w := n / 8)
    (fun j hj => by rw [w, hbt]; exact in_scr hw (by rw [eK]; omega))
    (fun j hj => by
      rw [rd, hxt]
      have := Nat.mul_le_mul_left n (show c ≤ 2 by omega)
      exact ⟨_, List.mem_append_left _ hr, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hbt, hxt, h8n]
      exact (hX (o := n * c) (l := n) (by have := Nat.mul_le_mul_left n (show c ≤ 2 by omega); omega)).symm.sub_left
        (Offset.sub S (by rw [eK]; omega) (by rw [eK]; omega)))
    (by omega) (by rw [eK]; omega)) fun u cp => ?_
  rw [hbt, hxt, h8n] at cp
  have hcs : bytesAt u.mem (at' S (Layout.oKeys + 32 * c)) n = bytesAt s.mem (X + BitVec.ofNat 64 (n * c)) n := by
    rw [bytesAt_eq_of (m' := t.mem) (b := X + BitVec.ofNat 64 (n * c)) fun q hq => cp.bytes q hq]
    exact bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hX (by have := Nat.mul_le_mul_left n (show c ≤ 2 by omega); omega)) (by omega)
  refine ⟨fun g h => by rw [cp.gpr _ h, hg _ h], by rw [cp.rd, rd], by rw [cp.wr, w], fun c' hc' => ?_, ?_⟩
  · by_cases e : c' = c
    · subst e; exact hcs
    · rw [bytesAt_frame cp.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact disj_scr S (by omega) (by rw [eK]; omega) (by rw [eK]; omega)) (by omega)]
      exact kc c' (by omega)
  · exact f.trans (cp.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by rw [eK]; omega) (by rw [eK]; omega)⟩)

theorem laneA_eq (k : Nat) : Layout.laneA k = 3296 + 128 * k := rfl
theorem laneB_eq (k : Nat) : Layout.laneB k = 3808 + 2208 * k := rfl

/-- The lanes, from `oA` to `oN`. -/
abbrev lanesR (S : Addr) : Region := ⟨at' S Layout.oA, 9344⟩

/-- After `k` pairs of copies of `seedLanes`: `PK.seed` in the lanes `A` and `B` below `k`. -/
def SeedI (n : Nat) (s : State) (S : Addr) (k : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ k' < k, bytesAt t.mem (at' S (Layout.laneA k')) n = bytesAt s.mem (at' S Layout.oPkSeed) n ∧
      bytesAt t.mem (at' S (Layout.laneB k')) n = bytesAt s.mem (at' S Layout.oPkSeed) n) ∧
    Frame [lanesR S] s.mem t.mem

theorem seed_ok {p : Params} (hn : p.n ≤ 32) (h8 : p.n % 8 = 0) {s : State} {S : Addr} (hb : s.gpr .rbx = S)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (seedLanes p)) s (SeedI p.n s S 4) := by
  have eP : Layout.oPkSeed = 3232 := rfl
  have eA : Layout.oA = 3296 := rfl
  have h8n : 8 * (p.n / 8) = p.n := by omega
  refine wp_flatMap (P := SeedI p.n s S) 4 ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    fun k hk t ⟨hg, rd, w, sd, f⟩ => ?_
  have hbt : t.gpr .rbx = S := by rw [hg _ (by decide), hb]
  have hpk : bytesAt t.mem (at' S Layout.oPkSeed) p.n = bytesAt s.mem (at' S Layout.oPkSeed) p.n :=
    bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by rw [eP, eA]; omega) (by rw [eP]; omega) (by rw [eA]; omega)) (by omega)
  have hsub : ∀ {o : Nat}, Layout.oA ≤ o → o + p.n ≤ 12640 → Region.Sub ⟨at' S o, p.n⟩ (lanesR S) :=
    fun {o} h₁ h₂ => Offset.sub S (by omega) (by rw [eA] at *; omega)
  refine WP.block_append (copyS_ok hbt (by rw [w]; exact hw) (d₁ := Layout.oPkSeed) (d₂ := Layout.laneA k)
    (w := p.n / 8) (by rw [eP]; omega) (by rw [laneA_eq]; omega) (by rw [eP, laneA_eq]; omega)
    fun u gu ru wu bu fu => ?_)
  have hbu : u.gpr .rbx = S := by rw [gu _ (by decide), hbt]
  rw [h8n] at bu fu
  refine copyS_ok hbu (by rw [wu, w]; exact hw) (d₁ := Layout.oPkSeed) (d₂ := Layout.laneB k)
    (w := p.n / 8) (by rw [eP]; omega) (by rw [laneB_eq]; omega) (by rw [eP, laneB_eq]; omega)
    fun v gv rv wv bv fv => ?_
  rw [h8n] at bv fv
  have dAB : Region.Disjoint ⟨at' S (Layout.laneB k), p.n⟩ ⟨at' S (Layout.laneA k), p.n⟩ :=
    disj_scr S (by rw [laneA_eq, laneB_eq]; omega) (by rw [laneB_eq]; omega) (by rw [laneA_eq]; omega)
  have hpku : bytesAt u.mem (at' S Layout.oPkSeed) p.n = bytesAt t.mem (at' S Layout.oPkSeed) p.n :=
    bytesAt_frame fu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by rw [eP, laneA_eq]; omega) (by rw [eP]; omega) (by rw [laneA_eq]; omega)) (by omega)
  refine ⟨fun g h => by rw [gv _ h, gu _ h, hg _ h], by rw [rv, ru, rd], by rw [wv, wu, w], fun k' hk' => ?_, ?_⟩
  · by_cases e : k' = k
    · subst e
      refine ⟨?_, by rw [bv, hpku, hpk]⟩
      rw [bytesAt_frame fv (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dAB.symm) (by omega),
        bu, hpk]
    · have ⟨ha, hb'⟩ := sd k' (by omega)
      have dA : ∀ {o : Nat}, o = Layout.laneA k ∨ o = Layout.laneB k →
          Region.Disjoint ⟨at' S (Layout.laneA k'), p.n⟩ ⟨at' S o, p.n⟩ := fun {o} ho => by
        rcases ho with rfl | rfl
        · exact disj_scr S (by rw [laneA_eq, laneA_eq]; omega) (by rw [laneA_eq]; omega) (by rw [laneA_eq]; omega)
        · exact disj_scr S (by rw [laneA_eq, laneB_eq]; omega) (by rw [laneA_eq]; omega) (by rw [laneB_eq]; omega)
      have dB : ∀ {o : Nat}, o = Layout.laneA k ∨ o = Layout.laneB k →
          Region.Disjoint ⟨at' S (Layout.laneB k'), p.n⟩ ⟨at' S o, p.n⟩ := fun {o} ho => by
        rcases ho with rfl | rfl
        · exact disj_scr S (by rw [laneB_eq, laneA_eq]; omega) (by rw [laneB_eq]; omega) (by rw [laneA_eq]; omega)
        · exact disj_scr S (by rw [laneB_eq, laneB_eq]; omega) (by rw [laneB_eq]; omega) (by rw [laneB_eq]; omega)
      refine ⟨?_, ?_⟩
      · rw [bytesAt_frame fv (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dA (.inr rfl)) (by omega),
          bytesAt_frame fu (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dA (.inl rfl)) (by omega), ha]
      · rw [bytesAt_frame fv (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dB (.inr rfl)) (by omega),
          bytesAt_frame fu (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dB (.inl rfl)) (by omega), hb']
  · refine f.trans ((fu.sub fun r hr => ?_).trans (fv.sub fun r hr => ?_)) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, hsub (by rw [laneA_eq, eA]; omega) (by rw [laneA_eq]; omega)⟩
    · exact ⟨_, List.mem_singleton_self _, hsub (by rw [laneB_eq, eA]; omega) (by rw [laneB_eq]; omega)⟩

/-! ## The addresses of the lanes -/

theorem bytesAt_split (m : Mem) (S : Addr) (a x y : Nat) :
    bytesAt m (at' S a) (x + y) = bytesAt m (at' S a) x ++ bytesAt m (at' S (a + x)) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, at_add, Nat.add_assoc]

/-- Lane `k` of `A` (`b = 0`) or `B`. -/
abbrev lane (k b : Nat) : Nat := if b = 0 then Layout.laneA k else Layout.laneB k

theorem lane_lt {k b : Nat} (hk : k < 4) : lane k b + 48 ≤ 12640 ∧ Layout.oA ≤ lane k b := by
  simp only [lane, laneA_eq, laneB_eq, show Layout.oA = 3296 from rfl]; split <;> omega

/-- Two lanes' addresses of `n ≤ 32`, 16 bytes each, are disjoint. -/
theorem lane_disj {n k b k' b' : Nat} (hn : n ≤ 32) (hk : k < 4) (hk' : k' < 4) (hb : b < 2) (hb' : b' < 2)
    (h : k ≠ k' ∨ b ≠ b') {S : Addr} {i j l l' : Nat} (hi : i + l ≤ 16) (hj : j + l' ≤ 16) :
    Region.Disjoint ⟨at' S (lane k b + n + i), l⟩ ⟨at' S (lane k' b' + n + j), l'⟩ := by
  have h1 := lane_lt (b := b) hk
  have h2 := lane_lt (b := b') hk'
  refine disj_scr S ?_ (by omega) (by omega)
  simp only [lane, laneA_eq, laneB_eq] at h1 h2 ⊢
  split <;> split <;> omega

/-- A lane's `PK.seed` and a lane's address are disjoint. -/
theorem seed_adrs_disj {n k b k' b' : Nat} (hn : n ≤ 32) (hk : k < 4) (hk' : k' < 4) {S : Addr} :
    Region.Disjoint ⟨at' S (lane k' b'), n⟩ ⟨at' S (lane k b + n), 16⟩ := by
  have h1 := lane_lt (b := b) hk
  have h2 := lane_lt (b := b') hk'
  refine disj_scr S ?_ (by omega) (by omega)
  simp only [lane, laneA_eq, laneB_eq] at h1 h2 ⊢
  split <;> split <;> omega

theorem bswap64_zero : bswap64 (0 : BitVec 64) = 0 := by decide

theorem zero_bytes8 : ((List.range (64 / 8)).map fun d => (0 : BitVec 64).extractLsb' (8 * d) 8) = toByte 0 8 := by
  decide

theorem layerTree_eq (L : Nat) : Proof.SlhDsa.layerTree L 0 = toByte L 4 ++ (toByte 0 4 ++ toByte 0 8) := by
  simp only [Proof.SlhDsa.layerTree]; congr 1

/-- After `j` of the eight addresses of `treeLanes`. -/
def TreeI (n L : Nat) (s : State) (S : Addr) (j : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ k < 4, ∀ b < 2, 2 * k + b < j → bytesAt t.mem (at' S (lane k b + n)) 16 = Proof.SlhDsa.layerTree L 0) ∧
    (∀ k < 4, ∀ b < 2, bytesAt t.mem (at' S (lane k b)) n = bytesAt s.mem (at' S (lane k b)) n) ∧
    Frame [lanesR S] s.mem t.mem

theorem item_ok {p : Params} (hn : p.n ≤ 32) {L : Nat} (hL : L < 2 ^ 32) {s : State} {S : Addr}
    (hb : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (h10 : (s.gpr .r10).toNat = L)
    (h11 : s.gpr .r11 = 0) {k b : Nat} (hk : k < 4) (hb2 : b < 2) {t : State} (ht : TreeI p.n L s S (2 * k + b) t) :
    WP isa (.block (setFieldR .rbx (lane k b + p.n) .r10 ++ setField .rbx (lane k b + p.n + 4) 0 ++
      ([.store (Impl.Sha3.X86_64.at_ .rbx (lane k b + p.n + 8)) .r11] : List Instr))) t
      (TreeI p.n L s S (2 * k + b + 1)) := by
  obtain ⟨hg, rd, w, ad, sd, f⟩ := ht
  have eA : Layout.oA = 3296 := rfl
  have hl := lane_lt (b := b) hk
  have hbt : t.gpr .rbx = S := by rw [hg _ (by decide), hb]
  have hwt : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [w]; exact hw
  rw [List.append_assoc]
  refine setFieldR_ok (by decide) (by rw [hg _ (by decide), h10]; exact hL)
    (by rw [hbt]; exact in_scr hwt (by omega)) fun u₁ p₁ => ?_
  refine setField_ok (by decide) (by decide) (by rw [p₁.gpr _ (by decide), hbt, p₁.wr]; exact in_scr hwt (by omega))
    fun u₂ p₂ => ?_
  have hb₂ : u₂.gpr .rbx = S := by rw [p₂.gpr _ (by decide), p₁.gpr _ (by decide), hbt]
  refine wp_store (a := at' S (lane k b + p.n + 8)) (by rw [ea_at, hb₂])
    (by rw [p₂.wr, p₁.wr]; exact in_scr hwt (by omega)) fun u₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_
  rw [hbt, hg _ (by decide), h10] at p₁
  rw [p₁.gpr _ (by decide), hbt] at p₂
  have h11' : u₂.gpr .r11 = 0 := by rw [p₂.gpr _ (by decide), p₁.gpr _ (by decide), hg _ (by decide), h11]
  -- the three fields
  have e₃ : bytesAt u₃.mem (at' S (lane k b + p.n + 8)) 8 = toByte 0 8 := by
    rw [m₃, h11', show (8 : Nat) = 64 / 8 from rfl, bytesAt_writeW _ (by decide) (by decide), zero_bytes8]
  have e₂ : bytesAt u₃.mem (at' S (lane k b + p.n + 4)) 4 = toByte 0 4 := by
    rw [m₃, ← p₂.bytes]
    exact bytesAt_frame (frame_writeW _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by omega) (by omega)) (by omega)
  have e₁ : bytesAt u₃.mem (at' S (lane k b + p.n)) 4 = toByte L 4 := by
    rw [m₃, ← p₁.bytes, bytesAt_frame (frame_writeW _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by omega) (by omega)) (by omega)]
    exact bytesAt_frame p₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr S (by omega) (by omega) (by omega)) (by omega)
  have hF : Frame [⟨at' S (lane k b + p.n), 16⟩] t.mem u₃.mem := by
    rw [m₃]
    refine ((p₁.frame.sub fun r hr => ?_).trans (p₂.frame.sub fun r hr => ?_)).trans
      ((frame_writeW _ _ _).sub fun r hr => ?_) <;> simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩
  refine ⟨fun g h => by rw [g₃, p₂.gpr _ h, p₁.gpr _ h, hg _ h], by rw [r₃, p₂.rd, p₁.rd, rd],
    by rw [w₃, p₂.wr, p₁.wr, w], fun k' hk' b' hb' hj => ?_, fun k' hk' b' hb' => ?_, ?_⟩
  · by_cases e : k' = k ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := e
      rw [show (16 : Nat) = 4 + (4 + 8) from rfl, bytesAt_split, bytesAt_split, layerTree_eq,
        show lane k' b' + p.n + 4 + 4 = lane k' b' + p.n + 8 by omega, e₁, e₂, e₃]
    · rw [bytesAt_frame hF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := lane_disj (S := S) (i := 0) (j := 0) (l := 16) (l' := 16) hn hk' hk hb' hb2
          (by omega) (by omega) (by omega)
        simpa using this) (by omega)]
      exact ad k' hk' b' hb' (by omega)
  · rw [bytesAt_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact seed_adrs_disj hn hk hk') (by omega)]
    exact sd k' hk' b' hb'
  · exact f.trans (hF.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩)

theorem tree_ok {p : Params} (hn : p.n ≤ 32) {L : Nat} (hL : L < 2 ^ 32) {s : State} {S : Addr}
    (hb : s.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (h10 : (s.gpr .r10).toNat = L)
    (h9 : s.gpr .r9 = 0) {Q : State → Prop}
    (k : ∀ t u, (∀ g, g ≠ .rax → g ≠ .r11 → u.gpr g = s.gpr g) → TreeI p.n L t S 8 u → t.mem = s.mem →
      t.rd = s.rd → t.wr = s.wr → Q u) :
    WP isa (.block (treeLanes p .r10 .r9)) s Q := by
  unfold treeLanes
  refine wp_mov fun t₁ u₁ => ?_
  refine VG.Proof.Sha3.X86_64.WP.cons rfl ?_
  generalize ht₂ : t₁.setReg .rax (bswap64 (t₁.gpr .rax)) = t₂
  have u₂ : Upd t₁ t₂ .rax (bswap64 (t₁.gpr .rax)) := ht₂ ▸ Upd.setReg _ _ _
  refine wp_mov fun t₃ u₃ => ?_
  have h11 : t₃.gpr .r11 = 0 := by rw [u₃.gpr, u₂.gpr, u₁.gpr, h9, bswap64_zero]
  have hb₃ : t₃.gpr .rbx = S := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb]
  have hw₃ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₃.wr := by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw
  have h10₃ : (t₃.gpr .r10).toNat = L := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h10]
  have hm₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (wp_flatMap (P := fun k => TreeI p.n L t₃ S (2 * k)) 4
    ⟨fun _ _ => rfl, rfl, rfl, fun _ _ _ _ h => absurd h (by omega), fun _ _ _ _ => rfl, Frame.refl _ _⟩
    fun k hk t ht => ?_) fun u hu => k t₃ u (fun g h₁ h₂ => ?_) hu hm₃ (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr])
  · refine wp_flatMap (P := fun b => TreeI p.n L t₃ S (2 * k + b)) 2 ht fun b hb2 t' ht' => ?_
    exact item_ok hn hL hb₃ hw₃ h10₃ h11 hk hb2 ht'
  · rw [hu.1 _ h₁, u₃.other _ h₂, u₂.other _ h₁, u₁.other _ h₁]

/-! ## The prologue -/

/-- The first block of `keyGen`. -/
abbrev proCode (p : Params) : List Instr :=
  kgSave .rcx ++ [.mov .rbx (.reg .rcx), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx)] ++
    rcTable ++ (List.range 3).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rdi (p.n * c) (p.n / 8)) ++
    seedLanes p ++ [.mov32 .r10 (.imm (BitVec.ofNat 32 (p.d - 1))), .mov32 .r9 (.imm 0)] ++ treeLanes p .r10 .r9 ++
    [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 0xffffffff), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 Layout.oSigTmp))]

/-- After the prologue, from the entry `σ` with `scratch = S` and `seeds = X`. -/
structure KPro (p : Params) (σ : State) (S X : Addr) (s : State) : Prop where
  bx : s.gpr .rbx = S
  rdi : s.gpr .rdi = S
  rsi : s.gpr .rsi = BitVec.ofNat 64 0xffffffff
  rdx : s.gpr .rdx = at' S Layout.oSigTmp
  r12 : s.gpr .r12 = σ.gpr .rsi
  r13 : s.gpr .r13 = σ.gpr .rdx
  sp : s.gpr .rsp = σ.gpr .rsp
  keep : ∀ r, r = .rbp ∨ r = .r14 ∨ r = .r15 → s.gpr r = σ.gpr r
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  saved : ∀ i < 6, s.mem.readW (at' S (oKgSave + 8 * i)) 64 = σ.gpr (savedRegs.getD i .rbx)
  keys : ∀ c < 3, bytesAt s.mem (at' S (Layout.oKeys + 32 * c)) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n
  env : Env p s.mem S (bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n) (Proof.SlhDsa.layerTree (p.d - 1) 0)
  frame : Frame [⟨S, 2 ^ 16⟩] σ.mem s.mem

theorem pro_ok {p : Params} (hn : p.n ≤ 32) (h8 : p.n % 8 = 0) (hd : p.d - 1 < 2 ^ 31) {σ : State} {S X : Addr}
    (hS : σ.gpr .rcx = S) (hX : σ.gpr .rdi = X) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr)
    (hr : (⟨X, 3 * p.n⟩ : Region) ∈ σ.rd) (hXf : X.toNat + 3 * p.n ≤ 2 ^ 64)
    (hdis : Region.Disjoint ⟨X, 3 * p.n⟩ ⟨S, 2 ^ 16⟩) :
    WP isa (.block (proCode p)) σ (KPro p σ S X) := by
  have eK : Layout.oKeys = 3168 := rfl
  have eA : Layout.oA = 3296 := rfl
  have eP : Layout.oPkSeed = 3232 := rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have e2 : oKgSave = 34080 := rfl
  simp only [proCode, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (save_ok (s := σ) (by rw [hS]; exact hw)) fun t₁ h₁ => ?_)
  have sv₁ : ∀ i < 6, t₁.mem.readW (at' S (oKgSave + 8 * i)) 64 = σ.gpr (savedRegs.getD i .rbx) := by
    rw [← hS]; exact h₁.saved
  have f₁ : Frame [⟨at' S oKgSave, 48⟩] σ.mem t₁.mem := by rw [← hS]; exact h₁.frame
  refine wp_mov fun t₂ u₂ => wp_mov fun t₃ u₃ => wp_mov fun t₄ u₄ => ?_
  have hb₄ : t₄.gpr .rbx = S := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h₁.gpr, hS]
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₄.wr := by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr]; exact hw
  have hm₄ : t₄.mem = t₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  refine WP.block_append (WP.mono (rc_ok hb₄ hw₄) fun t₅ ⟨g₅, rd₅, w₅, rc₅, f₅⟩ => ?_)
  have hb₅ : t₅.gpr .rbx = S := by rw [g₅ _ (by decide), hb₄]
  have hx₅ : t₅.gpr .rdi = X := by
    rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h₁.gpr, hX]
  have hw₅ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₅.wr := by rw [w₅]; exact hw₄
  have hr₅ : (⟨X, 3 * p.n⟩ : Region) ∈ t₅.rd := by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, h₁.rd]; exact hr
  refine WP.block_append (WP.mono (keys_ok hn h8 hb₅ hx₅ hw₅ hr₅ hXf hdis) fun t₆ ⟨g₆, rd₆, w₆, k₆, f₆⟩ => ?_)
  have hb₆ : t₆.gpr .rbx = S := by rw [g₆ _ (by decide), hb₅]
  have hw₆ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₆.wr := by rw [w₆]; exact hw₅
  refine WP.block_append (WP.mono (seed_ok hn h8 hb₆ hw₆) fun t₇ ⟨g₇, rd₇, w₇, s₇, f₇⟩ => ?_)
  refine wp_mov32i fun t₈ u₈ => wp_mov32i fun t₉ u₉ => ?_
  have hb₉ : t₉.gpr .rbx = S := by rw [u₉.other _ (by decide), u₈.other _ (by decide), g₇ _ (by decide), hb₆]
  have hw₉ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₉.wr := by rw [u₉.wr, u₈.wr, w₇]; exact hw₆
  have h10 : (t₉.gpr .r10).toNat = p.d - 1 := by
    rw [u₉.other _ (by decide), u₈.gpr]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have h9 : t₉.gpr .r9 = 0 := by rw [u₉.gpr]; rfl
  have hm₉ : t₉.mem = t₇.mem := by rw [u₉.mem, u₈.mem]
  refine WP.block_append (tree_ok hn (by omega) hb₉ hw₉ h10 h9 fun t₁₀ u hgu hu hm₁₀ hr₁₀ hw₁₀ => ?_)
  obtain ⟨g₁₀, rd₁₀, w₁₀, ad₁₀, sd₁₀, f₁₀⟩ := hu
  have hbu : u.gpr .rbx = S := by rw [hgu _ (by decide) (by decide), hb₉]
  refine wp_mov fun v₁ e₁ => wp_mov32i fun v₂ e₂ => wp_mov fun v₃ e₃ => wp_addi fun v₄ e₄ => WP.block_nil ?_
  have hmv : v₄.mem = u.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  -- registers
  have gv : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → v₄.gpr g = u.gpr g := fun g h₁ h₂ h₃ => by
    rw [e₄.other _ h₃, e₃.other _ h₃, e₂.other _ h₂, e₁.other _ h₁]
  -- the chain of states before `u`, register by register
  have gu : ∀ g, g ≠ .rax → g ≠ .r11 → g ≠ .r10 → g ≠ .r9 → g ≠ .rbx → g ≠ .r12 → g ≠ .r13 →
      u.gpr g = σ.gpr g := fun g a b c d e f' h => by
    rw [hgu _ a b, u₉.other _ d, u₈.other _ c, g₇ _ a, g₆ _ a, g₅ _ a, u₄.other _ h, u₃.other _ f', u₂.other _ e,
      h₁.gpr]
  have hW : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → (o + 8 ≤ Layout.oKeys ∨
      (Layout.oKeys + 96 ≤ o ∧ o + 8 ≤ Layout.oA) ∨ 12640 ≤ o) →
      u.mem.readW (at' S o) 64 = t₆.mem.readW (at' S o) 64 := fun {o} hl ho => by
    have d₁ : ∀ r ∈ [lanesR S], Region.Disjoint ⟨at' S o, 8⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S (by omega) hl (by omega)
    rw [Thash4Avx.readW_frame f₁₀ d₁, hm₁₀, hm₉, Thash4Avx.readW_frame f₇ d₁]
  have hW₅ : ∀ {o : Nat}, o + 8 ≤ 2 ^ 16 → (o + 8 ≤ Layout.oKeys ∨
      (Layout.oKeys + 96 ≤ o ∧ o + 8 ≤ Layout.oA) ∨ 12640 ≤ o) →
      t₆.mem.readW (at' S o) 64 = t₅.mem.readW (at' S o) 64 := fun {o} hl ho =>
    Thash4Avx.readW_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S (by omega) hl (by omega)
  -- the seeds, outside `scratch`
  have hXs : ∀ c < 3, bytesAt t₅.mem (X + BitVec.ofNat 64 (p.n * c)) p.n =
      bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n := fun c hc => by
    have := Nat.mul_le_mul_left p.n (show c ≤ 2 by omega)
    have hd' : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
        Region.Disjoint ⟨X + BitVec.ofNat 64 (p.n * c), p.n⟩ ⟨at' S o, l⟩ := fun {o l} h =>
      (hdis.sub_left (Offset.sub_base X (by omega))).sub_right (Offset.sub_base S h)
    rw [bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd' (by omega)) (by omega), hm₄,
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd' (by omega)) (by omega)]
  have hkeys : ∀ c < 3, bytesAt u.mem (at' S (Layout.oKeys + 32 * c)) p.n =
      bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n := fun c hc => by
    have d₁ : ∀ r ∈ [lanesR S], Region.Disjoint ⟨at' S (Layout.oKeys + 32 * c), p.n⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S (by omega) (by omega) (by omega)
    rw [bytesAt_frame f₁₀ d₁ (by omega), hm₁₀, hm₉, bytesAt_frame f₇ d₁ (by omega), k₆ c hc, hXs c hc]
  have hpk : bytesAt t₆.mem (at' S Layout.oPkSeed) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n := by
    rw [← hXs 2 (by decide), ← k₆ 2 (by decide)]; rfl
  have hseed : ∀ k < 4, ∀ b < 2, bytesAt u.mem (at' S (lane k b)) p.n =
      bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n := fun k hk b hb => by
    rw [sd₁₀ k hk b hb, hm₁₀, hm₉, ← hpk]
    have := s₇ k hk
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · exact this.1
    · exact this.2
  refine ⟨by rw [gv _ (by decide) (by decide) (by decide), hbu], by rw [e₄.other _ (by decide),
      e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, hbu], by
      rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₄.gpr, e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hbu, Levels.sx_ofNat (by omega)]
  · rw [gv _ (by decide) (by decide) (by decide), hgu _ (by decide) (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), h₁.gpr]
  · rw [gv _ (by decide) (by decide) (by decide), hgu _ (by decide) (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), h₁.gpr]
  · rw [gv _ (by decide) (by decide) (by decide)]
    exact gu _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro r hr
    rcases hr with rfl | rfl | rfl
    all_goals
      rw [gv _ (by decide) (by decide) (by decide)]
      exact gu _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd, rd₁₀, hr₁₀, u₉.rd, u₈.rd, rd₇, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
  · rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr, w₁₀, hw₁₀, u₉.wr, u₈.wr, w₇, w₆, w₅, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
  · intro i hi
    rw [hmv, hW (by omega) (by omega), hW₅ (by omega) (by omega),
      Thash4Avx.readW_frame f₅ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S (by omega) (by omega) (by omega),
      hm₄]
    exact sv₁ i hi
  · intro c hc; rw [hmv]; exact hkeys c hc
  · refine ⟨fun r hr k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [hmv, show S + BitVec.ofNat 64 (1600 + 32 * r + 8 * k) = at' S (1600 + 32 * r + 8 * k) from rfl,
        hW (by omega) (by omega), hW₅ (by omega) (by omega)]
      exact rc₅ r hr k hk
    · rw [hmv]; exact hseed k hk 0 (by decide)
    · rw [hmv]; exact hseed k hk 1 (by decide)
    · rw [hmv]; exact ad₁₀ k hk 0 (by decide) (by omega)
    · rw [hmv]; exact ad₁₀ k hk 1 (by decide) (by omega)
  · have hsub : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → ∀ r ∈ [(⟨at' S o, l⟩ : Region)],
        ∃ r' ∈ [(⟨S, 2 ^ 16⟩ : Region)], Region.Sub r r' := fun {o l} h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Levels.sub_scr S h⟩
    have r₄ : Frame [⟨S, 2 ^ 16⟩] t₁.mem t₄.mem := by rw [hm₄]; exact Frame.refl _ _
    have r₁₀ : Frame [⟨S, 2 ^ 16⟩] t₇.mem t₁₀.mem := by rw [hm₁₀, hm₉]; exact Frame.refl _ _
    rw [hmv]
    exact (f₁.sub (hsub (by omega))).trans (r₄.trans ((f₅.sub (hsub (by omega))).trans
      ((f₆.sub (hsub (by omega))).trans ((f₇.sub (hsub (by omega))).trans (r₁₀.trans (f₁₀.sub (hsub (by omega))))))))

end VG.Proof.SlhDsa.X86_64.KeyGen
