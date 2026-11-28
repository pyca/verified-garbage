module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsFront
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public import VerifiedGarbage.Proof.SlhDsa.VerifySpec
public import VerifiedGarbage.Proof.SlhDsa.VerifyTopSpec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: what holds throughout, the prologue, a lane's tree

`forsPk(scratch = x0, sig = x1, kp = x2)` (`Impl/SlhDsa/AArch64/Verify.lean`)
saves the caller's `x19`–`x27` and `x30` in frame 2 (`slotsF`), keeps
`scratch`, `kp` and `sig` in `x19`–`x21` and computes the FORS indices
(`entry_ok`). Throughout (`FK`), it keeps those, the caller's `x28`, the
stack pointer, the permissions, the low halves of `v8`–`v15`, `Env`, the
saved registers and the indices, and changes memory only in `changes p S`.
A group's steps write only `gw` (`work`, the lanes `A` but their `PK.seed`
and `a16`, the roots in lane 0 of `B`), which keeps all of that (`FK.keep`).

Each lane's tree `min(t₀ + k, k - 1)` (`treeT_ok`) and its signature
(`treeSig_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr bytesAt_frame readW_frame byte_frame env_frame
  regions_scr)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-! ## The parameters -/

/-- The parameters `forsPk` is proved for (`X86_64.FPar`, with `Sz`). -/
structure FP (p : Params) : Prop where
  sz : Sz p
  a1 : 1 ≤ p.a
  a : p.a ≤ 14
  k1 : 1 ≤ p.k
  k : p.k ≤ 35
  md : p.mdLen = (p.k * p.a + 7) / 8
  ka : p.k * p.a ≤ 8 * 61

theorem fp_of (hz : Sz p) (hp : X86_64.ForsCT.P6 p) : FP p := by
  have hmd : p.mdLen = (p.k * p.a + 7) / 8 := rfl
  rcases hp with ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ | ⟨_, ha, hk⟩ <;>
    exact ⟨hz, by omega, by omega, by omega, by omega, hmd, by rw [ha, hk]; decide⟩

theorem FP.n32 (h : FP p) : p.n ≤ 32 := h.sz.n32
theorem FP.n16 (h : FP p) : 16 ≤ p.n := h.sz.n16
theorem FP.n8 (h : FP p) : p.n % 8 = 0 := h.sz.n8
theorem FP.nv (h : FP p) : p.n = 16 ∨ p.n = 24 ∨ p.n = 32 := h.sz.nv

theorem FP.pa (h : FP p) : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) h.a

theorem FP.kn (h : FP p) : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul h.k h.n32

/-- A tree's leaves, below `2³²`. -/
theorem FP.leaf (h : FP p) {t i : Nat} (ht : t < p.k) (hi : i < 2 ^ p.a) : t * 2 ^ p.a + i < 2 ^ 32 := by
  have : (t + 1) * 2 ^ p.a ≤ 35 * 2 ^ 14 := Nat.mul_le_mul (by have := h.k; omega) h.pa
  rw [Nat.succ_mul] at this; omega

theorem forsSigLen_eq (p : Params) : p.forsSigLen = p.n * (p.k * (p.a + 1)) := by
  simp only [Params.forsSigLen, Nat.add_comm 1 p.a, Nat.mul_comm _ p.n]

/-- Tree `t`'s nodes in the signature: node `j ≤ a` (0 its private key value). -/
theorem forsSig_le {t : Nat} (ht : t < p.k) {j : Nat} (hj : j ≤ p.a) :
    p.n * (t * (p.a + 1)) + p.n * j + p.n ≤ p.forsSigLen := by
  rw [forsSigLen_eq, ← Nat.mul_add, ← Nat.mul_succ]
  refine Nat.mul_le_mul_left _ ?_
  have : (t + 1) * (p.a + 1) ≤ p.k * (p.a + 1) := Nat.mul_le_mul_right _ ht
  rw [Nat.succ_mul] at this; omega

/-! ## The layout -/

theorem laneA_eq (k : Nat) : Layout.laneA k = 3136 + 128 * k := rfl
theorem laneB0_eq : Layout.laneB 0 = 3648 := rfl
theorem oFidx_eq : Layout.oFidx = 2048 := rfl
theorem oDigest_eq : Layout.oDigest = 1792 := rfl
theorem oMsg_eq : Layout.oMsg = 1984 := rfl

/-- Frame 2's slots of the registers `forsPk` saves. -/
def slotsF : List (Reg × Nat) :=
  [(.x19, 1280), (.x20, 1288), (.x21, 1296), (.x22, 1304), (.x23, 1312), (.x24, 1320), (.x25, 1328),
    (.x26, 1336), (.x27, 1344), (.x30, 1352)]

theorem fpro_eq : Impl.SlhDsa.AArch64.Verify.fpro =
    Spill.saveCode .x0 slotsF ++ ([.addImm .x .x19 .x0 0, .addImm .x .x21 .x1 0, .addImm .x .x20 .x2 0] : List Instr) :=
  rfl

theorem slotsF_in : ∀ q ∈ slotsF, 1280 ≤ q.2 ∧ q.2 + 8 ≤ 1360 := by decide
theorem slotsF_ok : ∀ q ∈ slotsF, q.2 % 8 = 0 ∧ q.2 < 32768 := by decide

/-! ## What holds throughout -/

/-- The entry state `σ`, with `scratch` at `S` and the signature at `sig`. -/
structure Ctx (p : Params) (σ : State) (S sig : Addr) : Prop where
  x0 : σ.gpr .x0 = S
  x1 : σ.gpr .x1 = sig
  R : Regions σ S [⟨sig, p.forsSigLen⟩] ⟨S, 0⟩
  kp : (σ.gpr .x2).toNat < 2 ^ 32

theorem Ctx.scr {σ : State} {S sig : Addr} (c : Ctx p σ S sig) : (⟨S, 65536⟩ : Region) ∈ σ.wr := regions_scr c.R

theorem Ctx.fit {σ : State} {S sig : Addr} (c : Ctx p σ S sig) : S.toNat + 65536 ≤ 2 ^ 64 := c.R.scr_fit

theorem Ctx.sigR {σ : State} {S sig : Addr} (c : Ctx p σ S sig) : (⟨sig, p.forsSigLen⟩ : Region) ∈ σ.rd := by
  rw [c.R.rd_eq]; exact List.mem_singleton_self _

theorem Ctx.sfit {σ : State} {S sig : Addr} (c : Ctx p σ S sig) : sig.toNat + p.forsSigLen ≤ 2 ^ 64 :=
  c.R.rd_fit _ (List.mem_singleton_self _)

theorem Ctx.sss {σ : State} {S sig : Addr} (c : Ctx p σ S sig) : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 65536⟩ :=
  c.R.rd_scr _ (List.mem_singleton_self _)

/-- What holds throughout, with `PK.seed` `pk`, the tree's `a16` `a`, the indices `I`. -/
structure FK (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (t : State) : Prop where
  x19 : t.gpr .x19 = S
  x20 : t.gpr .x20 = σ.gpr .x2
  x21 : t.gpr .x21 = sig
  x28 : t.gpr .x28 = σ.gpr .x28
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  env : Env p t.mem S pk a
  saved : Spill.Saved S σ.gpr slotsF t.mem
  fidx : ∀ i < p.k, t.mem.readW (at' S (Layout.oFidx + 8 * i)) 64 = BitVec.ofNat 64 (I i)
  frame : Frame (changes p S) σ.mem t.mem

/-- What a group's steps write. -/
def tailA (p : Params) (S : Addr) (k : Nat) : Region := ⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩

def gw (p : Params) (S : Addr) : List Region :=
  ⟨S, workUsed⟩ :: (List.range 4).map (tailA p S) ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩]

theorem tailA_gw (S : Addr) {k : Nat} (hk : k < 4) : tailA p S k ∈ gw p S :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

theorem work_gw (S : Addr) : (⟨S, workUsed⟩ : Region) ∈ gw p S := List.mem_cons_self

theorem roots_gw (S : Addr) : (⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩ : Region) ∈ gw p S :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem gw_changes (hF : FP p) (S : Addr) : ∀ r ∈ gw p S, ∃ R ∈ changes p S, Region.Sub r R := by
  have hn := hF.n32
  have hkn := hF.kn
  intro r hr
  simp only [gw, List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | ⟨k, hk, rfl⟩) | rfl
  · exact ⟨_, by simp [changes], fun _ h => h⟩
  · refine ⟨_, ?_, fun _ h => h⟩
    simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range]
    exact .inl (.inr ⟨k, hk, List.mem_cons_self⟩)
  · refine ⟨⟨at' S (Layout.laneB 0 + p.n + 16), Layout.strideB - p.n - 16⟩, ?_, ?_⟩
    · simp only [changes, laneTails, List.mem_append, List.mem_flatMap, List.mem_range]
      exact .inl (.inr ⟨0, by decide, List.mem_cons_of_mem _ List.mem_cons_self⟩)
    · exact Offset.sub S (by omega) (by simp only [Layout.strideB, laneB0_eq]; omega)

/-- A part of `scratch` past `work`, outside the lanes `A`'s tails and the roots, is outside `gw`. -/
theorem gw_disj (hF : FP p) (S : Addr) {o l : Nat} (h₀ : workUsed ≤ o) (h₁ : o + l ≤ 65536)
    (hA : ∀ k < 4, o + l ≤ 3136 + 128 * k + p.n + 16 ∨ 3136 + 128 * (k + 1) ≤ o)
    (hB : o + l ≤ 3648 + p.n + 32 ∨ 3648 + p.n + 32 + p.k * p.n ≤ o) :
    ∀ r ∈ gw p S, Region.Disjoint ⟨at' S o, l⟩ r := by
  have hn := hF.n32
  have hkn := hF.kn
  intro r hr
  simp only [gw, List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | ⟨k, hk, rfl⟩) | rfl
  · have := disj_scr (o := o) (l := l) (o' := 0) (l' := workUsed) S (by omega) h₁ (by simp only [workUsed]; omega)
    simpa using this
  · have := hA k hk
    simp only [tailA, laneA_eq, Layout.strideA]
    exact disj_scr S (by omega) h₁ (by omega)
  · rw [laneB0_eq]; exact disj_scr S hB h₁ (by omega)

theorem changes_scr (hF : FP p) (S : Addr) : ∀ r ∈ changes p S, Region.Sub r ⟨S, 65536⟩ := by
  have hn := hF.n32
  intro r hr
  simp only [changes, laneTails, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with ((h | h) | ⟨k, hk, h | h⟩) | (h | h | h | h | h) <;> subst h
  · exact Region.sub_prefix (by simp [workUsed])
  all_goals first
    | exact Offset.sub_base S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
    | exact Offset.sub_base S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
    | exact Offset.sub_base S (by simp only [Layout.oVars, Layout.frameLen]; omega)
    | exact Offset.sub_base S (by simp only [Layout.oDigits]; omega)
    | exact Offset.sub_base S (by simp only [Layout.oN, Layout.nodeSlots]; omega)
    | exact Offset.sub_base S (by simp only [Layout.oRoots, Layout.oN, Layout.nodeSlots]; omega)
    | exact Offset.sub_base S (by simp only [Layout.oMsg]; omega)
    | exact Offset.sub_base S (by simp only [Layout.oFidx]; omega)

/-- `Env` past a frame apart from the lanes' `PK.seed` and `a16`. -/
theorem env_keep {m m' : Mem} {S : Addr} {pk a : List Byte} {rs : List Region} (he : Env p m S pk a)
    (hf : Frame rs m m')
    (hd : ∀ k < 4, ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.laneA k), p.n + 16⟩ r ∧
      Region.Disjoint ⟨at' S (Layout.laneB k), p.n + 16⟩ r) (hn : p.n ≤ 32) : Env p m' S pk a := by
  have sub : ∀ (o x l : Nat), x + l ≤ p.n + 16 →
      Region.Sub ⟨at' S (o + x), l⟩ ⟨at' S o, p.n + 16⟩ := fun o x l h => by
    rw [← TreeBase.at_add]; exact Offset.sub_base _ h
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [← he.seedA k hk, ← Nat.add_zero (Layout.laneA k)]
    exact bytesAt_frame hf (fun r hr => ((hd k hk r hr).1).sub_left (sub _ 0 p.n (by omega))) (by omega)
  · rw [← he.seedB k hk, ← Nat.add_zero (Layout.laneB k)]
    exact bytesAt_frame hf (fun r hr => ((hd k hk r hr).2).sub_left (sub _ 0 p.n (by omega))) (by omega)
  · rw [← he.adrsA k hk]
    exact bytesAt_frame hf (fun r hr => ((hd k hk r hr).1).sub_left (sub _ p.n 16 (by omega))) (by omega)
  · rw [← he.adrsB k hk]
    exact bytesAt_frame hf (fun r hr => ((hd k hk r hr).2).sub_left (sub _ p.n 16 (by omega))) (by omega)

/-- `gw` keeps `Env`. -/
theorem env_gw (hF : FP p) {m m' : Mem} {S : Addr} {pk a : List Byte} (he : Env p m S pk a)
    (hf : Frame (gw p S) m m') : Env p m' S pk a := by
  have hn := hF.n32
  have hkn := hF.kn
  refine env_keep he hf (fun k hk r hr => ⟨?_, ?_⟩) hn
  · rw [laneA_eq]
    exact gw_disj hF S (by simp only [workUsed]; omega) (by omega) (fun j hj => by omega) (by omega) r hr
  · simp only [Layout.laneB, Layout.oB, Layout.strideB]
    exact gw_disj hF S (by simp only [workUsed]; omega) (by omega) (fun j hj => by omega) (by omega) r hr

/-- `FK` past a step that writes only `gw` and keeps `x19`–`x21` and `x28`. -/
theorem FK.keep {σ : State} {S sig : Addr} {pk a : List Byte} {I : Nat → Nat} {t t' : State} (hF : FP p)
    (h : FK p σ S sig pk a I t) {rs : List Reg} (hk : Keep rs t t') (h19 : Reg.x19 ∉ rs) (h20 : Reg.x20 ∉ rs)
    (h21 : Reg.x21 ∉ rs) (h28 : Reg.x28 ∉ rs) (hf : Frame (gw p S) t.mem t'.mem) : FK p σ S sig pk a I t' := by
  have hn := hF.n32
  have hkn := hF.kn
  have hk35 := hF.k
  refine ⟨by rw [hk.gpr _ h19, h.x19], by rw [hk.gpr _ h20, h.x20], by rw [hk.gpr _ h21, h.x21],
    by rw [hk.gpr _ h28, h.x28], by rw [hk.sp, h.sp], by rw [hk.rd, h.rd], by rw [hk.wr, h.wr],
    fun r hr => by rw [hk.vcs r hr, h.vcs r hr], env_gw hF h.env hf, ?_, fun i hi => ?_, ?_⟩
  · refine h.saved.frame_in (lo := 1280) (n := 80) slotsF_in hf fun r hr => ?_
    exact gw_disj hF S (by simp only [workUsed]; omega) (by omega) (fun j hj => by omega) (by omega) r hr
  · rw [readW_frame hf fun r hr => gw_disj hF S (by rw [oFidx_eq]; simp only [workUsed]; omega)
      (by rw [oFidx_eq]; omega) (fun j hj => by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega) r hr, h.fidx i hi]
  · exact h.frame.trans (hf.sub (gw_changes hF S))

/-- The signature's bytes are the entry's. -/
theorem FK.sig {σ : State} {S sig : Addr} {pk a : List Byte} {I : Nat → Nat} {t : State} (hF : FP p)
    (c : Ctx p σ S sig) (h : FK p σ S sig pk a I t) {o l : Nat} (hol : o + l ≤ p.forsSigLen) :
    bytesAt t.mem (sig + BitVec.ofNat 64 o) l = bytesAt σ.mem (sig + BitVec.ofNat 64 o) l :=
  bytesAt_frame h.frame (fun r hr => (c.sss.sub_left (Offset.sub_base sig hol)).sub_right (changes_scr hF S r hr))
    (by have := c.sfit; omega)

/-! ## The prologue and the indices -/

/-- The indices, from the digest's bytes at the entry. -/
abbrev Ix (p : Params) (m : Mem) (S : Addr) : Nat → Nat := Fors.ixv m S p.a

theorem ix_lt (m : Mem) (S : Addr) (t : Nat) : Ix p m S t < 2 ^ p.a := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem entry_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    (hE : Env p σ.mem S pk a) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.fpro ++ Impl.SlhDsa.AArch64.Fors.indices p.a p.k ++
      ([.movz .x .x22 0 0] : List Instr))) σ fun t =>
      FK p σ S sig pk a (Ix p σ.mem S) t ∧ t.gpr .x22 = BitVec.ofNat 64 0 := by
  have hn32 := hF.n32
  have hwS := c.scr
  have hS := c.x0
  rw [fpro_eq, List.append_assoc, List.append_assoc]
  refine Spill.save_ok slotsF_ok (fun q hq => by
    rw [hS]; have := slotsF_in q hq; exact in_scr hwS (by omega)) ?_
  have hsv : Spill.Saved S σ.gpr slotsF (Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slotsF) := by
    rw [← hS]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf₁ : Frame [⟨at' S 1280, 80⟩] σ.mem (Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slotsF) := by
    rw [← hS]; exact Spill.saveMem_frame slotsF_in (by decide) _ _ _
  generalize Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slotsF = m₁ at hsv hf₁
  simp only [List.cons_append, List.nil_append]
  refine MlKem.AArch64.wp_addImm (by decide) fun t₁ o₁ e₁ => MlKem.AArch64.wp_addImm (by decide) fun t₂ o₂ e₂ =>
    MlKem.AArch64.wp_addImm (by decide) fun t₃ o₃ e₃ => ?_
  have h19 : t₃.gpr .x19 = S := by rw [o₃.get .x19, o₂.get .x19, e₁, BitVec.add_zero]; exact hS
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [o₃.wr, o₂.wr, o₁.wr]; exact hwS
  have hm₃ : t₃.mem = m₁ := by rw [o₃.mem, o₂.mem, o₁.mem]
  refine Fors.indices_ok hF.a (by have := hF.k; omega) hF.ka h19 hw₃ fun t₄ ix => ?_
  refine MlKem.AArch64.wp_movz fun t₅ o₅ e₅ => WP.block_nil ?_
  have hfi : Frame [⟨at' S Layout.oFidx, 8 * p.k⟩] m₁ t₅.mem := by rw [o₅.mem, ← hm₃]; exact ix.frame
  have hd₁ : ∀ {o l : Nat}, (o + l ≤ 1280 ∨ 1360 ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S 1280, 80⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact disj_scr S h₁ h₂ (by omega)
  have hd₂ : ∀ {o l : Nat}, (o + l ≤ Layout.oFidx ∨ Layout.oFidx + 8 * p.k ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S Layout.oFidx, 8 * p.k⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S h₁ h₂ (by rw [oFidx_eq]; have := hF.k; omega)
  have hF₅ : Frame ([(⟨at' S 1280, 80⟩ : Region)] ++ [⟨at' S Layout.oFidx, 8 * p.k⟩]) σ.mem t₅.mem :=
    (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hfi.mono fun r hr => List.mem_append_right _ hr)
  have hix : ∀ i < p.k, Ix p t₃.mem S i = Ix p σ.mem S i := fun i hi => by
    have hia : i * p.a / 8 + 3 ≤ 64 := by
      have := Nat.mul_le_mul_right p.a (show i + 1 ≤ p.k by omega)
      have := hF.ka; rw [Nat.succ_mul] at *; omega
    have kb : ∀ x, x < 3 → m₁ (at' S (Layout.oDigest + i * p.a / 8 + x)) =
        σ.mem (at' S (Layout.oDigest + i * p.a / 8 + x)) := fun x hx =>
      byte_frame hf₁ (hd₁ (by rw [oDigest_eq]; omega) (by rw [oDigest_eq]; omega))
    simp only [Ix, Fors.ixv, hm₃]
    rw [show Layout.oDigest + i * p.a / 8 = Layout.oDigest + i * p.a / 8 + 0 from rfl, kb 0 (by decide),
      kb 1 (by decide), kb 2 (by decide)]
  have hkeep : ∀ {o l : Nat}, (1360 ≤ o ∧ o + l ≤ Layout.oFidx) ∨ (Layout.oFidx + 8 * p.k ≤ o ∧ o + l ≤ 65536) ∨
      o + l ≤ 1280 →
      ∀ r ∈ [(⟨at' S 1280, 80⟩ : Region)] ++ [⟨at' S Layout.oFidx, 8 * p.k⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
    intro o l ho r hr
    rw [oFidx_eq] at ho
    rcases List.mem_append.mp hr with hr | hr
    · exact hd₁ (by omega) (by omega) r hr
    · exact hd₂ (by rw [oFidx_eq]; omega) (by omega) r hr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r _ => ?_, ?_, ?_, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [o₅.get .x19, ix.gpr _ (by decide) (by decide), h19]
  · rw [o₅.get .x20, ix.gpr _ (by decide) (by decide), e₃, o₂.get .x2, o₁.get .x2, BitVec.add_zero]
  · rw [o₅.get .x21, ix.gpr _ (by decide) (by decide), o₃.get .x21, e₂, o₁.get .x1, BitVec.add_zero]; exact c.x1
  · rw [o₅.get .x28, ix.gpr _ (by decide) (by decide), o₃.get .x28, o₂.get .x28, o₁.get .x28]
  · rw [o₅.sp, ix.sp, o₃.sp, o₂.sp, o₁.sp]
  · rw [o₅.rd, ix.rd, o₃.rd, o₂.rd, o₁.rd]
  · rw [o₅.wr, ix.wr, o₃.wr, o₂.wr, o₁.wr]
  · rw [o₅.vcs r ‹_›, ix.vr, o₃.vcs r ‹_›, o₂.vcs r ‹_›, o₁.vcs r ‹_›]
  · have hk35 := hF.k
    exact env_frame hn32 hE hF₅ fun ho₁ ho₂ => hkeep (.inr (.inl ⟨by rw [oFidx_eq]; simp only [Layout.oA] at ho₁; omega,
      by simp only [Layout.oN] at ho₂; omega⟩))
  · exact hsv.frame_in (lo := 1280) (n := 80) slotsF_in hfi fun r hr => hd₂ (by rw [oFidx_eq]; omega) (by omega) r hr
  · rw [o₅.mem, ix.idx i hi]; exact congrArg _ (hix i hi)
  · refine hF₅.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨at' S Layout.oVars, 4 * Layout.frameLen⟩, by simp [changes],
        Offset.sub S (by simp [Layout.oVars]) (by simp [Layout.oVars, Layout.frameLen])⟩
    · exact ⟨⟨at' S Layout.oFidx, 320⟩, by simp [changes], Region.sub_prefix (by have := hF.k; omega)⟩
  · rw [e₅]; rfl

/-! ## Arithmetic -/

theorem lt_bit {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  split
  · rename_i h
    rw [BitVec.toNat_ofNat]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = 2 ^ 64 - (b - a) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e]
    show _ = 1
    omega
  · rename_i h
    rw [BitVec.toNat_ofNat]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = a - b := by
      rw [show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    show _ = 0
    omega

theorem neg_bit (q : Prop) [Decidable q] :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if q then 1 else 0)) = if q then BitVec.allOnes 64 else 0 := by
  by_cases h : q <;> simp [h] <;> decide

/-- `c₀ - ((c₀ - L) & mask)`, `mask` all ones iff `c₀ > L`. -/
theorem clamp_eq {c₀ L : Nat} (hc : c₀ < 2 ^ 62) (hL : L < 2 ^ 62) :
    BitVec.ofNat 64 c₀ - ((BitVec.ofNat 64 c₀ - BitVec.ofNat 64 L) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 L - BitVec.ofNat 64 c₀) >>> 63)) = BitVec.ofNat 64 (min c₀ L) := by
  rw [lt_bit (by omega) (by omega), neg_bit]
  by_cases h : L < c₀
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]
    rw [Nat.min_eq_right (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · simp [h]
    rw [Nat.min_eq_left (by omega)]

theorem imm16 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ## A lane's tree and its signature -/

/-- Lane `k`'s tree in the group from `t₀`. -/
abbrev tOf (p : Params) (t₀ k' : Nat) : Nat := min (t₀ + k') (p.k - 1)

/-- Tree `t`'s private key value's offset in the signature. -/
abbrev sigOff (p : Params) (t : Nat) : Nat := p.n * (t * (p.a + 1))

theorem tOf_lt (hF : FP p) (t₀ k' : Nat) : tOf p t₀ k' < p.k := by have := hF.k1; simp only [tOf]; omega

theorem treeT_ok (hF : FP p) {k' t₀ : Nat} (hk' : k' < 4) (ht : t₀ < 2 ^ 32) {s : State}
    (h22 : s.gpr .x22 = BitVec.ofNat 64 t₀) {is : List Instr} {Q : State → Prop}
    (K : ∀ s', Only [.x10, .x13, .x14, .x15] s s' → s'.gpr .x10 = BitVec.ofNat 64 (tOf p t₀ k') →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.treeT p k' ++ is)) s Q := by
  have hk := hF.k
  simp only [Impl.SlhDsa.AArch64.Verify.treeT, List.append_assoc, List.cons_append, List.nil_append]
  refine MlKem.AArch64.wp_addImm (by omega) fun s₁ o₁ e₁ => movV_ok (by omega) fun s₂ o₂ e₂ => ?_
  refine MlKem.AArch64.wp_sub fun s₃ o₃ e₃ => MlKem.AArch64.wp_lsr (by decide) fun s₄ o₄ e₄ =>
    MlKem.AArch64.wp_subImm (by omega) fun s₅ o₅ e₅ => MlKem.AArch64.wp_movz fun s₆ o₆ e₆ =>
    MlKem.AArch64.wp_sub fun s₇ o₇ e₇ => MlKem.AArch64.wp_and fun s₈ o₈ e₈ => MlKem.AArch64.wp_sub fun s₉ o₉ e₉ => ?_
  have v₁ : s₂.gpr .x10 = BitVec.ofNat 64 (t₀ + k') := by rw [o₂.get .x10, e₁, h22, BitVec.ofNat_add]
  have v₄ : s₄.gpr .x10 = BitVec.ofNat 64 (t₀ + k') := by rw [o₄.get .x10, o₃.get .x10, v₁]
  refine K s₉ ((o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉)))))))).mono
    (by decide)) ?_
  rw [e₉, e₈, o₈.get .x10, o₇.get .x10, o₆.get .x10, o₅.get .x10, v₄, e₇, o₇.get .x14, o₆.get .x14, e₅, v₄,
    o₆.get .x13, e₆, o₅.get .x13, e₄, e₃, e₂, o₂.get .x10, e₁, h22, ← BitVec.ofNat_add,
    show (0 : BitVec 16).setWidth 64 = BitVec.ofNat 64 0 from rfl]
  exact clamp_eq (c₀ := t₀ + k') (L := p.k - 1) (by omega) (by omega)

theorem treeSig_ok {t : Nat} (hF : FP p) {s : State} {sig : Addr}
    (h10 : s.gpr .x10 = BitVec.ofNat 64 t) (h21 : s.gpr .x21 = sig) {is : List Instr} {Q : State → Prop}
    (K : ∀ s', Only [.x13, .x12] s s' → s'.gpr .x12 = sig + BitVec.ofNat 64 (sigOff p t) →
      WP isa (.block is) s' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.treeSig p ++ is)) s Q := by
  have hn := hF.n32
  have ha := hF.a
  have han : (p.a + 1) * p.n ≤ 15 * 32 := Nat.mul_le_mul (by omega) hn
  simp only [Impl.SlhDsa.AArch64.Verify.treeSig, List.append_assoc, List.cons_append, List.nil_append]
  refine movV_ok (by omega) fun s₁ o₁ e₁ => MlKem.AArch64.wp_mul fun s₂ o₂ e₂ =>
    MlKem.AArch64.wp_add fun s₃ o₃ e₃ => K s₃ ((o₁.trans (o₂.trans o₃)).mono (by decide)) ?_
  rw [e₃, o₂.get .x21, o₁.get .x21, h21, e₂, o₁.get .x10, h10, e₁, BitVec.ofNat_mul_ofNat, BitVec.add_comm, sigOff,
    Nat.mul_comm (p.a + 1) p.n, Nat.mul_left_comm]

end VG.Proof.SlhDsa.AArch64.ForsPk
