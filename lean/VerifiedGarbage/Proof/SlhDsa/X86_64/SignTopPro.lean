module

-- separate module: the frame's prologue, whose many stores elaborate slowly, apart from the body

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopCtx
public import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGenPro
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsMain
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsGroup
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsCTBase

/-!
# SLH-DSA (SHAKE) on x86-64, `sign`: the frame's prologue

Untrusted: everything here is checked by Lean. From the frame's push
(`Pushed`), the first block of `signBody`: the formatted message's second
byte, the callee-saved registers saved at `oKgSave`, the round constants,
the four keys at `oKeys`, and `PK.seed` in every lane, which give `Ctx`
(`pro_ok`); and the two pointers it loads from the frame, which its
constant-time proof splits it at (`proA_ok`, `proB_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs copyWords)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave kgSave rcTable seedLanes stk fHdr fScr fKey)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_store wp_store8 ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (in_scr in_scr' at_add disj_scr scr0)

/-- The values the frame's push stores, from `SP` up. -/
def SL.vals (L : SL) : List (BitVec 64) :=
  [0, L.S, L.rnd, L.sig, L.ctxLen, L.ctx, L.len, L.msg, L.sk]

/-- After the frame's push: `g` the registers, `m₀` the memory on entry. -/
structure Pushed (L : SL) (g : Reg → BitVec 64) (m₀ : Mem) (u : State) : Prop where
  rd : u.rd = L.rd
  wr : u.wr = L.FR :: [L.SIG, L.SCR]
  rsp : u.gpr .rsp = L.SP
  gpr : ∀ r ∈ calleeSaved, r ≠ .rsp → u.gpr r = g r
  r8 : u.gpr .r8 = L.ctxLen
  slot : ∀ j (hj : j < 9), u.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 = L.vals[j]'(by simp [SL.vals]; omega)
  frame : Frame [L.SCR, L.STK, L.SIG] m₀ u.mem

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  congr 1

/-! ## Saving the callee-saved registers -/

/-- After `kgSave b`. -/
structure SavePost (b : Reg) (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  saved : ∀ i < 6, t.mem.readW (at' (s.gpr b) (oKgSave + 8 * i)) 64 = s.gpr (savedRegs.getD i .rbx)
  frame : Frame [⟨at' (s.gpr b) oKgSave, 48⟩] s.mem t.mem

theorem save_ok (b : Reg) {s : State} (hw : (⟨s.gpr b, 2 ^ 16⟩ : Region) ∈ s.wr) :
    WP isa (.block (kgSave b)) s (SavePost b s) := by
  have e2 : oKgSave = 34080 := rfl
  have hc : ∀ j < 6, Region.Contains ⟨at' (s.gpr b) oKgSave, 48⟩ (at' (s.gpr b) (oKgSave + 8 * j)) 8 :=
    fun j hj => by
      rw [← at_add]
      exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (Levels.wp_rangeMap (P := fun j t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ i < j, t.mem.readW (at' (s.gpr b) (oKgSave + 8 * i)) 64 = s.gpr (savedRegs.getD i .rbx)) ∧
      Frame [⟨at' (s.gpr b) oKgSave, 48⟩] s.mem t.mem) 6
    ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩ fun j hj t ⟨g, r, w, sv, f⟩ => ?_)
    fun t ⟨g, r, w, sv, f⟩ => ⟨g, r, w, sv, f⟩
  refine wp_store (a := at' (s.gpr b) (oKgSave + 8 * j)) (by rw [ea_at, g]) (by
    rw [w, e2]; exact in_scr hw (by omega)) fun t' g' m' r' w' => WP.block_nil ?_
  refine ⟨by rw [g', g], by rw [r', r], by rw [w', w], fun i hi => ?_, ?_⟩
  · rw [m']
    by_cases e : i = j
    · subst e; rw [Mem.readW_writeW_self64, g]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by rw [e2]; omega) (by rw [e2]; omega)
        (by rw [e2]; omega)) (by decide), sv i (by omega)]
  · rw [m']
    exact f.writeW (List.mem_singleton_self _) _ (hc j (by omega))

/-! ## The keys -/

/-- After `c` of the four copies. -/
def KeyI (n : Nat) (s : State) (S X : Addr) (c : Nat) (t : State) : Prop :=
  (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ c' < c, bytesAt t.mem (at' S (Layout.oKeys + 32 * c')) n = bytesAt s.mem (X + BitVec.ofNat 64 (n * c')) n) ∧
    Frame [⟨at' S Layout.oKeys, 128⟩] s.mem t.mem

theorem keys_ok {n : Nat} (hn : n ≤ 32) (h8 : n % 8 = 0) {s : State} {S X : Addr} (hb : s.gpr .rbx = S)
    (hx : s.gpr .rsi = X) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hr : (⟨X, 4 * n⟩ : Region) ∈ s.rd)
    (hXf : X.toNat + 4 * n ≤ 2 ^ 64) (hdis : Region.Disjoint ⟨X, 4 * n⟩ ⟨S, 2 ^ 16⟩) :
    WP isa (.block ((List.range 4).flatMap fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rsi (n * c) (n / 8))) s
      (KeyI n s S X 4) := by
  have eK : Layout.oKeys = 3168 := rfl
  have h8n : 8 * (n / 8) = n := by omega
  refine KeyGen.wp_flatMap (P := KeyI n s S X) 4 ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    fun c hc t ⟨hg, rd, w, kc, f⟩ => ?_
  have hbt : t.gpr .rbx = S := by rw [hg _ (by decide), hb]
  have hxt : t.gpr .rsi = X := by rw [hg _ (by decide), hx]
  have hX : ∀ {o l : Nat}, o + l ≤ 4 * n → Region.Disjoint ⟨X + BitVec.ofNat 64 o, l⟩ ⟨at' S Layout.oKeys, 128⟩ :=
    fun {o l} h => (hdis.sub_left (Offset.sub_base X (by omega))).sub_right (Offset.sub_base S (by rw [eK]; omega))
  have hc1 := Nat.mul_le_mul_left n (show c ≤ 3 by omega)
  refine WP.mono (copyWords_ok (s := t) (t := .rbx) (src := .rsi) (by decide) (by decide)
    (d₂ := Layout.oKeys + 32 * c) (d₁ := n * c) (w := n / 8)
    (fun j hj => by rw [w, hbt]; exact in_scr hw (by rw [eK]; omega))
    (fun j hj => by
      rw [rd, hxt]
      exact ⟨_, List.mem_append_left _ hr, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hbt, hxt, h8n]
      exact (hX (o := n * c) (l := n) (by omega)).symm.sub_left
        (Offset.sub S (by rw [eK]; omega) (by rw [eK]; omega)))
    (by omega) (by rw [eK]; omega)) fun u cp => ?_
  rw [hbt, hxt, h8n] at cp
  have hcs : bytesAt u.mem (at' S (Layout.oKeys + 32 * c)) n = bytesAt s.mem (X + BitVec.ofNat 64 (n * c)) n := by
    rw [KeyGen.bytesAt_eq_of (m' := t.mem) (b := X + BitVec.ofNat 64 (n * c)) fun q hq => cp.bytes q hq]
    exact bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hX (by omega)) (by omega)
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

/-! ## The prologue -/

/-- The first block of `signBody`, in the three pieces its constant-time
proof takes apart: the second byte of `M′` and `scratch`'s pointer; the
saves, `rbx`, and `sk`'s pointer; the rest. -/
abbrev proA : List Instr := [.store8 (stk (fHdr + 1)) .r8, .mov .rdi (.mem (stk fScr))]
abbrev proB : List Instr := kgSave .rdi ++ [.mov .rbx (.reg .rdi), .mov .rsi (.mem (stk fKey))]
abbrev proC (p : Params) : List Instr :=
  rcTable ++ (List.range 4).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rsi (p.n * c) (p.n / 8)) ++
    seedLanes p

theorem proCode_eq (p : Params) :
    (([.store8 (stk (fHdr + 1)) .r8, .mov .rdi (.mem (stk fScr))] : List Instr) ++ kgSave .rdi ++
      ([.mov .rbx (.reg .rdi), .mov .rsi (.mem (stk fKey))] : List Instr) ++ rcTable ++
      (List.range 4).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rsi (p.n * c) (p.n / 8)) ++
      seedLanes p : List Instr) = proA ++ (proB ++ proC p) := by
  simp only [proA, proB, proC, List.append_assoc, List.cons_append, List.nil_append]

theorem proA_ok {L : SL} (_hL : L.Ok) {g : Reg → BitVec 64} {m₀ : Mem} {u : State} (hu : Pushed L g m₀ u) :
    WP isa (.block proA) u fun v => v.gpr .rdi = L.S ∧ v.gpr .rsp = L.SP ∧ v.rd = u.rd ∧ v.wr = u.wr ∧
      v.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.sk := by
  refine wp_store8 (a := L.SP + BitVec.ofNat 64 1) (by rw [ea_stk, hu.rsp]; rfl)
    ⟨L.FR, by rw [hu.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩ fun u₁ g₁ m₁ r₁ w₁ => ?_
  refine wp_movm (a := L.SP + BitVec.ofNat 64 8) (by rw [ea_stk, g₁, hu.rsp]; rfl)
    ⟨L.FR, by rw [r₁, w₁, hu.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩ fun u₂ e₂ => WP.block_nil ?_
  refine ⟨?_, by rw [e₂.other _ (by decide), g₁, hu.rsp], by rw [e₂.rd, r₁], by rw [e₂.wr, w₁], ?_⟩
  · rw [e₂.gpr, m₁, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact hu.slot 1 (by omega)
  · rw [e₂.mem, m₁, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact hu.slot 8 (by omega)

theorem proB_ok {L : SL} (hL : L.Ok) {v : State} (hS : (⟨L.S, 2 ^ 16⟩ : Region) ∈ v.wr) (hdi : v.gpr .rdi = L.S)
    (hsp : v.gpr .rsp = L.SP) (hk : v.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.sk)
    (hin : InRegions (v.rd ++ v.wr) (L.SP + BitVec.ofNat 64 64) 8) :
    WP isa (.block proB) v fun w => w.gpr .rbx = L.S ∧ w.gpr .rsi = L.sk := by
  have eK : oKgSave = 34080 := rfl
  refine WP.block_append (WP.mono (save_ok .rdi (s := v) (by rw [hdi]; exact hS)) fun u₃ h₃ => ?_)
  refine wp_mov fun u₄ e₄ => wp_movm (a := L.SP + BitVec.ofNat 64 64)
    (by rw [ea_stk, e₄.other _ (by decide), h₃.gpr, hsp]; rfl)
    (by rw [e₄.rd, e₄.wr, h₃.rd, h₃.wr]; exact hin) fun u₅ e₅ => WP.block_nil ?_
  refine ⟨by rw [e₅.other _ (by decide), e₄.gpr, h₃.gpr, hdi], ?_⟩
  rw [e₅.gpr, e₄.mem, Thash4Avx.readW_frame h₃.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hdi]
    exact (hL.fr_scr (d := 64) (n := 8) (by omega)).sub_right (hL.scr_sub (by rw [eK]; omega)), hk]

theorem pro_ok {p : Params} {L : SL} (hL : L.Ok) (hn : L.n = p.n) {g : Reg → BitVec 64} {m₀ : Mem} {u : State}
    (hu : Pushed L g m₀ u) :
    WP isa (.block (([.store8 (stk (fHdr + 1)) .r8, .mov .rdi (.mem (stk fScr))] : List Instr) ++ kgSave .rdi ++
      ([.mov .rbx (.reg .rdi), .mov .rsi (.mem (stk fKey))] : List Instr) ++ rcTable ++
      (List.range 4).flatMap (fun c => copyWords .rbx (Layout.oKeys + 32 * c) .rsi (p.n * c) (p.n / 8)) ++
      seedLanes p)) u (Ctx L g m₀) := by
  have hn32 : p.n ≤ 32 := by have := hL.n; omega
  have h8 : p.n % 8 = 0 := by have := hL.n; omega
  have hnB := hL.nB
  have eK : oKgSave = 34080 := rfl
  have eP : Layout.oPkSeed = 3232 := rfl
  have eA : Layout.oA = 3296 := rfl
  have eY : Layout.oKeys = 3168 := rfl
  -- the frame's slots, apart from `scratch`
  have dS : ∀ {d l o k : Nat}, d + l ≤ 72 → o + k ≤ 65536 →
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, l⟩ ⟨at' L.S o, k⟩ :=
    fun h₁ h₂ => (hL.fr_scr h₁).sub_right (hL.scr_sub h₂)
  have hwS : (⟨L.S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hu.wr]; simp
  have slot : ∀ j (hj : j < 9), u.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 = L.vals[j]'(by simp [SL.vals]; omega) :=
    hu.slot
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `ctx_len` after the 0
  refine wp_store8 (a := L.SP + BitVec.ofNat 64 1) (by rw [ea_stk, hu.rsp]; rfl)
    ⟨L.FR, by rw [hu.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩ fun u₁ g₁ m₁ r₁ w₁ => ?_
  have sl₁ : ∀ j, 1 ≤ j → (hj : j < 9) → u₁.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 =
      L.vals[j]'(by simp [SL.vals]; omega) := fun j h1 hj => by
    rw [m₁, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), slot j hj]
  refine wp_movm (a := L.SP + BitVec.ofNat 64 8) (by rw [ea_stk, g₁, hu.rsp]; rfl)
    ⟨L.FR, by rw [r₁, w₁, hu.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩ fun u₂ e₂ => ?_
  have hdi₂ : u₂.gpr .rdi = L.S := by rw [e₂.gpr]; exact sl₁ 1 (by omega) (by omega)
  -- the callee-saved registers
  refine WP.block_append (WP.mono (save_ok .rdi (s := u₂) (by rw [hdi₂, e₂.wr, w₁]; exact hwS)) fun u₃ h₃ => ?_)
  have sv₃ := h₃.saved
  have fr₃ := h₃.frame
  rw [hdi₂] at sv₃ fr₃
  refine wp_mov fun u₄ e₄ => wp_movm (a := L.SP + BitVec.ofNat 64 64)
    (by rw [ea_stk, e₄.other _ (by decide), h₃.gpr, e₂.other _ (by decide), g₁, hu.rsp]; rfl)
    ⟨L.FR, by rw [e₄.rd, e₄.wr, h₃.rd, h₃.wr, e₂.rd, e₂.wr, r₁, w₁, hu.wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩ fun u₅ e₅ => ?_
  have hb₅ : u₅.gpr .rbx = L.S := by rw [e₅.other _ (by decide), e₄.gpr, h₃.gpr, hdi₂]
  have hm₅ : u₅.mem = u₃.mem := by rw [e₅.mem, e₄.mem]
  have hw₅ : u₅.wr = u.wr := by rw [e₅.wr, e₄.wr, h₃.wr, e₂.wr, w₁]
  have hr₅ : u₅.rd = u.rd := by rw [e₅.rd, e₄.rd, h₃.rd, e₂.rd, r₁]
  -- the slots after the save
  have sl₃ : ∀ j, 1 ≤ j → (hj : j < 9) → u₃.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 =
      L.vals[j]'(by simp [SL.vals]; omega) := fun j h1 hj => by
    rw [Thash4Avx.readW_frame fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dS (by omega) (by rw [eK]; omega), e₂.mem]
    exact sl₁ j h1 hj
  have hsi₅ : u₅.gpr .rsi = L.sk := by rw [e₅.gpr, e₄.mem]; exact sl₃ 8 (by omega) (by omega)
  -- the round constants
  refine WP.block_append (WP.mono (KeyGen.rc_ok hb₅ (by rw [hw₅]; exact hwS)) fun u₆ ⟨g₆, rd₆, w₆, rc₆, f₆⟩ => ?_)
  have hb₆ : u₆.gpr .rbx = L.S := by rw [g₆ _ (by decide), hb₅]
  have hsi₆ : u₆.gpr .rsi = L.sk := by rw [g₆ _ (by decide), hsi₅]
  -- the keys
  have hsk : (⟨L.sk, 4 * p.n⟩ : Region) ∈ u₆.rd := by rw [rd₆, hr₅, hu.rd, ← hn]; simp
  refine WP.block_append (WP.mono (keys_ok hn32 h8 hb₆ hsi₆ (by rw [w₆, hw₅]; exact hwS) hsk
    (by rw [← hn]; exact hL.nSk) (by rw [← hn]; exact hL.sSk.symm)) fun u₇ ⟨g₇, rd₇, w₇, k₇, f₇⟩ => ?_)
  have hb₇ : u₇.gpr .rbx = L.S := by rw [g₇ _ (by decide), hb₆]
  -- the lanes' `PK.seed`
  refine WP.mono (KeyGen.seed_ok hn32 h8 hb₇ (by rw [w₇, w₆, hw₅]; exact hwS)) fun t ⟨g₈, rd₈, w₈, s₈, f₈⟩ => ?_
  -- the registers
  have gt : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rbx → r ≠ .rdi → t.gpr r = u.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₈ _ h1, g₇ _ h1, g₆ _ h1, e₅.other _ h2, e₄.other _ h3, h₃.gpr, e₂.other _ h4, g₁]
  -- the memory: changes in `scratch` after the store
  have f₃ : Frame [⟨at' L.S oKgSave, 48⟩] u₁.mem u₃.mem := by rw [← e₂.mem]; exact fr₃
  have sub : ∀ {o k : Nat}, o + k ≤ 65536 → ∀ r ∈ [(⟨at' L.S o, k⟩ : Region)],
      ∃ r' ∈ [(⟨at' L.S 0, 65536⟩ : Region)], Region.Sub r r' := fun {o k} h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub L.S (by omega) (by omega)⟩
  have f₆' : Frame [⟨at' L.S 0, 65536⟩] u₁.mem u₆.mem := by
    rw [hm₅] at f₆
    exact (f₃.sub (sub (by rw [eK]; omega))).trans (f₆.sub (sub (by omega)))
  have hfS : Frame [⟨at' L.S 0, 65536⟩] u₁.mem t.mem :=
    f₆'.trans ((f₇.sub (sub (by rw [eY]; omega))).trans (f₈.sub (sub (by rw [eA]; omega))))
  have dS0 : ∀ {d l : Nat}, d + l ≤ 72 → ∀ r ∈ [(⟨at' L.S 0, 65536⟩ : Region)],
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, l⟩ r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dS h (by omega)
  have slt : ∀ j, 1 ≤ j → (hj : j < 9) → t.mem.readW (L.SP + BitVec.ofNat 64 (8 * j)) 64 =
      L.vals[j]'(by simp [SL.vals]; omega) := fun j h1 hj => by
    rw [Thash4Avx.readW_frame hfS (dS0 (by omega))]; exact sl₁ j h1 hj
  -- the private key, as on entry
  have f₁ : Frame [⟨L.SP + BitVec.ofNat 64 1, 1⟩] u.mem u₁.mem := by
    rw [m₁]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hsk₀ : ∀ c < 4, bytesAt u₆.mem (L.sk + BitVec.ofNat 64 (p.n * c)) p.n =
      bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * c)) p.n := fun c hc => by
    have hc1 : p.n * c + p.n ≤ 4 * L.n := by
      have := Nat.mul_le_mul_left p.n (show c + 1 ≤ 4 by omega); rw [hn]; rw [Nat.mul_succ] at this; omega
    have hsub : Region.Sub ⟨L.sk + BitVec.ofNat 64 (p.n * c), p.n⟩ L.SK := Offset.sub_base L.sk hc1
    rw [bytesAt_frame f₆' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.sSk.symm.sub_left hsub).sub_right (Offset.sub_base (d := 0) (n := 65536) (k := 65536) L.S (by omega)))
        (by omega),
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hL.kSk.sub_left (hL.fr_stk (d := 1) (n := 1) (by omega))).symm).sub_left hsub) (by omega)]
    exact bytesAt_frame hu.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.sSk.symm.sub_left hsub
      · exact hL.kSk.symm.sub_left hsub
      · exact hL.gSk.symm.sub_left hsub) (by omega)
  -- `scratch`'s keys after the lanes
  have hkey : ∀ c < 4, bytesAt t.mem (at' L.S (Layout.oKeys + 32 * c)) p.n =
      bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * c)) p.n := fun c hc => by
    rw [bytesAt_frame f₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact disj_scr L.S (by rw [eY, eA]; omega) (by rw [eY]; omega) (by rw [eA]; omega)) (by omega), k₇ c hc]
    exact hsk₀ c hc
  have hseed : bytesAt u₇.mem (at' L.S Layout.oPkSeed) p.n = bytesAt m₀ (L.sk + BitVec.ofNat 64 (p.n * 2)) p.n := by
    rw [show Layout.oPkSeed = Layout.oKeys + 32 * 2 from rfl, k₇ 2 (by decide)]; exact hsk₀ 2 (by decide)
  -- the saved registers and the round constants, kept by what follows
  have hsr : ∀ i < 6, savedRegs.getD i .rbx ≠ .rdi ∧ savedRegs.getD i .rbx ∈ calleeSaved ∧
      savedRegs.getD i .rbx ≠ .rsp := fun i hi => by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have sv : ∀ i < 6, t.mem.readW (at' L.S (oKgSave + 8 * i)) 64 = g (savedRegs.getD i .rbx) := fun i hi => by
    rw [Thash4Avx.readW_frame f₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact disj_scr L.S (by rw [eK, eA]; omega) (by rw [eK]; omega) (by rw [eA]; omega)),
      Thash4Avx.readW_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact disj_scr L.S (by rw [eK, eY]; omega) (by rw [eK]; omega) (by rw [eY]; omega)),
      Thash4Avx.readW_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact disj_scr L.S (by rw [eK]; omega) (by rw [eK]; omega) (by omega)), hm₅, sv₃ i hi,
      e₂.other _ (hsr i hi).1, g₁, hu.gpr _ (hsr i hi).2.1 (hsr i hi).2.2]
  have ncs : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdi := fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- the formatted message's two bytes
  have hdr : bytesAt t.mem L.SP 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat] := by
    have e₀ : bytesAt t.mem L.SP 2 = bytesAt u₁.mem L.SP 2 :=
      bytesAt_frame hfS (fun r hr => by have := dS0 (d := 0) (l := 2) (by omega) r hr; simpa using this) (by omega)
    rw [e₀, m₁, show (2 : Nat) = 1 + 1 from rfl, KeyGen.bytesAt_add]
    have b₂ := bytesAt_writeW (m := u.mem) (a := L.SP + BitVec.ofNat 64 1) ((u.gpr .r8).setWidth 8) (by decide) (by decide)
    simp only [Nat.reduceDiv] at b₂
    rw [b₂, bytesAt_frame (Frame.writeW (Frame.refl [⟨L.SP + BitVec.ofNat 64 1, 1⟩] u.mem)
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)) (by omega)]
    have h0 := slot 0 (by omega)
    simp only [SL.vals, List.getElem_cons_zero] at h0
    have ez : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => by simp
    have hb0 : u.mem (L.SP + BitVec.ofNat 64 0) = 0 := by
      have := ForsCT.fbyte_readW64 u.mem L.SP (j := 0) (by omega)
      rw [show 8 * 0 = 0 from rfl, ez] at h0
      rw [this, h0]; rfl
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, hb0]
    rw [hu.r8]
    refine List.cons_eq_cons.mpr ⟨by simp, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  refine ⟨by rw [rd₈, rd₇, rd₆, hr₅, hu.rd], by rw [w₈, w₇, w₆, hw₅, hu.wr],
    by rw [gt _ (by decide) (by decide) (by decide) (by decide), hu.rsp], by rw [g₈ _ (by decide), hb₇],
    fun r hr h1 h2 => by rw [gt r (ncs r hr).1 (ncs r hr).2.1 h2 (ncs r hr).2.2, hu.gpr r hr h1], sv,
    by simpa [SL.vals] using slt 1 (by omega) (by omega), by simpa [SL.vals] using slt 2 (by omega) (by omega),
    by simpa [SL.vals] using slt 3 (by omega) (by omega), by simpa [SL.vals] using slt 4 (by omega) (by omega),
    by simpa [SL.vals] using slt 5 (by omega) (by omega), by simpa [SL.vals] using slt 6 (by omega) (by omega),
    by simpa [SL.vals] using slt 7 (by omega) (by omega), by simpa [SL.vals] using slt 8 (by omega) (by omega),
    hdr, ?_, fun r hr k hk => ?_, fun c hc => by rw [hn]; exact hkey c hc, fun k hk => ?_, fun k hk => ?_⟩
  · refine hu.frame.trans ?_
    refine (f₁.sub fun r hr => ?_).trans (hfS.sub fun r hr => ?_) <;> simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨L.STK, by simp, hL.fr_stk (by omega)⟩
    · exact ⟨L.SCR, by simp, Offset.sub_base (d := 0) (n := 65536) (k := 65536) L.S (by omega)⟩
  · have := rc₆ r hr k hk
    rw [Thash4Avx.readW_frame f₈ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact disj_scr L.S (by rw [eA]; omega) (by omega) (by rw [eA]; omega)),
      Thash4Avx.readW_frame f₇ (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact disj_scr L.S (by rw [eY]; omega) (by omega) (by rw [eY]; omega))]
    exact this
  · rw [hn, (s₈ k hk).1, hseed]
  · rw [hn, (s₈ k hk).2, hseed]

end VG.Proof.SlhDsa.X86_64.SignTop
