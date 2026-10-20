module

public import VerifiedGarbage.Proof.Camellia.X86.Group
public import VerifiedGarbage.Proof.Camellia.X86.Keys
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Camellia ECB on x86 (32-bit): the whole function

As SM4's (`Proof/Sm4/X86/Ecb.lean`) and ARMv7's
(`Proof/Camellia/Arm/Ecb.lean`): `ecb_wp`, with the working space as the
fifth argument (`ecbX86`), `ecb dir` saves the callee-saved registers,
builds the table of subkeys for 18 or 24 rounds in the order `dir` uses
them, keeps the data pointer and the count in their slots, transforms the
blocks a group at a time (`dataLoop_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_)
open VG.Proof.Camellia (DInv outF blocksAt_of_dinv ecb_eq outF_spec schedWords_getD dirPerm dirPerm_lt)

/-- The specification's direction. -/
def specDir : Dir → Spec.Camellia.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86 with its working space as the fifth argument. -/
def ecbX86 (dir : Dir) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24)
  post s s' :=
    Spec.Camellia.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (specDir dir)
        (Spec.Camellia.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- The order of the subkeys in the table, for each direction. -/
def permOf (dir : Dir) : Nat → Nat → Nat := dirPerm (specDir dir)

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4)
    (hk : KeyPre s₀ b sched) (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4)
    (hr : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) :
    WP isa (keys dir g) s₀ (KeysPost s₀ b sched g (permOf dir g)) := by
  cases dir
  · exact encKeys_wp hg hk harg hr
  · exact decKeys_wp hg hk harg hr

/-! ## The arguments -/

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat} (hi : i < 5) :
    (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
  exact VG.Offset.contains _ (by omega) (by omega) (by omega)

/-- `mov eax, [esp + 4 + 4 i]; mov [edi + 4 k], eax`. -/
theorem argSlot_ok (s : State) {b : BitVec 32} {i k : Nat} (hb : s.gpr .edi = b) (hk : k < slots)
    (hw : ScrIn s.wr b) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] s = some s' ∧
      s'.gpr .eax = s.mem.readW (s.ea (argOp i)) 32 ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (s.ea (argOp i)) 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (k := k) (by rw [o₁ _ (by decide), hb]) hk
    (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, by rw [g₂, v₁], fun r hr => by rw [g₂, o₁ r hr], by rw [m₂, v₁, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁], by rw [← m₁]; exact f₂⟩
  rw [show ([.mov .eax (.mem (argOp i)), .store (slotAt .edi k) .eax] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.store (slotAt .edi k) .eax] from rfl, runBlock_app, e₁, Option.bind_some, e₂]

/-- `mov eax, [esp + 8]; cmp eax, 18`. -/
theorem cmpRounds_ok (s : State) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)] s = some s' ∧
      s'.zf = some (s.mem.readW (s.ea (argOp 1)) 32 - 18 == 0) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 1 ha
  let a := s₁.gpr .eax
  refine ⟨arithFlags s₁ (a - 18) (a.toNat < (18 : BitVec 32).toNat) (subOverflow a 18 (a - 18)), ?_,
    by rw [RegUpd.zf_arithFlags, show a = _ from v₁], fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr],
    by rw [RegUpd.mem_arithFlags, m₁], by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  rw [show ([.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)] : List Instr) =
    [.mov .eax (.mem (argOp 1))] ++ [.alu .cmp .eax (.imm 18)] from rfl, runBlock_app, e₁, Option.bind_some]
  rfl

/-! ## The table and the groups -/

/-- What the body needs: the prologue's work. -/
structure BodyPre (s₀ : State) (b sched D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem body_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) {g : Nat} (hg : g = 3 ∨ g = 4)
    (hgR : (arg s₀ 1).toNat / 6 = g) {s₁ : State}
    (h₁ : BodyPre s₀ (arg s₀ 4) (arg s₀ 0) (arg s₀ 2) (arg s₀ 3).toNat s₁) :
    WP isa (body dir g) s₁ (GDone s₀ (arg s₀ 4) (arg s₀ 2) (arg s₀ 3).toNat g
      fun i => (schedWords s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat).getD (permOf dir g i) 0) := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE, hR⟩ := hp
  let sched := arg s₀ 0
  let R := (arg s₀ 1).toNat
  let D := arg s₀ 2
  let n := (arg s₀ 3).toNat
  let b := arg s₀ 4
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (sched.setWidth 64) R).getD (permOf dir g i) 0
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  have hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched.setWidth 64, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  have hrA : (⟨argAddr s₀ 0, 20⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 5,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 5,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  have subS : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    fun k hk => slot_sub hfit' hk
  have hk₁ : KeyPre s₁ b sched :=
    ⟨h₁.base, by rw [h₁.wr]; exact hwS, List.mem_append_left _ (by rw [h₁.rd]; exact hrK), fitK, dKS⟩
  unfold body
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hg hk₁ (argIn h₁.rd h₁.wr h₁.esp 0 (by decide))
    (by rw [ea_arg h₁.esp]; exact argR h₁.frame 0 (by decide))) fun s₂ k₂ => ?_)
  have f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₂.mem :=
    h₁.frame.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [k₂.regs _ (by decide) (by decide), h₁.esp]
  have hE : ∀ i < 8 * g + 2,
      Spec.Camellia.wordAt s₁.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * permOf dir g i)) = E i :=
    fun i hi => by
      have hp : permOf dir g i < 8 * g + 2 := dirPerm_lt (specDir dir) hi
      rw [show E i = _ from schedWords_getD s₀.mem (sched.setWidth 64) (R := R)
        (by simp only [Spec.Camellia.scheduleLength]; omega)]
      exact hk₁.wordAt_eq h₁.frame (by omega)
  have sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨hg, fun i hi => hE i hi ▸ by rw [← base₂]; exact base₂ ▸ k₂.ent i hi, fun i hi => ?_⟩
    rw [← h₁.saved i hi]
    exact slot_keep hfit' (lo := savedSlot) (hi := slots) (Nat.le_refl _) k₂.frame
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by rw [savedSlot_eq, slots_eq] at *; omega))
      (by omega) (by rw [savedSlot_eq, slots_eq]; omega)
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, h₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, h₁.wr]
  -- The data pointer and the count to their slots.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a, f₃a⟩ := argSlot_ok s₂ (i := 2) (k := dSlot) base₂ (by decide)
    (by rw [wr₂]; exact hwS) (argIn rd₂ wr₂ esp₂ 2 (by decide))
  have f₀₃a : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃a.mem :=
    f₀₂.trans (f₃a.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact subS _ (by decide)⟩)
  have esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b, f₃b⟩ := argSlot_ok s₃a (i := 3) (k := nSlot)
    ((o₃a _ (by decide)).trans base₂) (by decide) (by rw [wr₃a, wr₂]; exact hwS)
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 3 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .eax &&& s₃b.gpr .eax) false false
  have e₃ : runBlock isa [.mov .eax (.mem (argOp 2)), st dSlot .eax, .mov .eax (.mem (argOp 3)), st nSlot .eax,
      .alu .test .eax (.reg .eax)] s₂ = some s₃ := by
    rw [show ([.mov .eax (.mem (argOp 2)), st dSlot .eax, .mov .eax (.mem (argOp 3)), st nSlot .eax,
        .alu .test .eax (.reg .eax)] : List Instr) =
      [.mov .eax (.mem (argOp 2)), .store (slotAt .edi dSlot) .eax] ++
        ([.mov .eax (.mem (argOp 3)), .store (slotAt .edi nSlot) .eax] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_app, e₃a, Option.bind_some, runBlock_app, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have eax₃ : s₃b.gpr .eax = arg s₀ 3 := by
    rw [a₃b, ea_arg esp₃a]; exact argR f₀₃a 3 (by decide)
  have dp₃ : s₃.mem.readW (wordAddr b dSlot) 32 = D := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := dSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_right (by decide),
      m₃a, readW_slot_write hfit' (j := dSlot) (k := dSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ea_arg esp₂]
    exact argR f₀₂ 2 (by decide)
  have np₃ : s₃.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 n := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := nSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ← a₃b, eax₃]
    simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f₃ : Frame [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩] s₂.mem s₃.mem :=
    (f₃a.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (f₃b.sub fun r hr => ⟨r, by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  have sc₃ : ScrOk s₀ b g E s₃.mem := sc₂.frame hfit' f₃ (dn_disj hfit')
  have f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₀₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, dn_sub hfit' r hr⟩)
  have data₃ : ∀ i < 16 * n, s₃.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₀₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega) hi
  have fr₃ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₃.mem :=
    f₀₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have g₃ : ∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r := fun r hr => by
    show s₃b.gpr r = _; rw [o₃b r hr, o₃a r hr]
  have base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide)]; exact base₂
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), esp₂]
  have rd₃ : s₃.rd = s₀.rd := by show s₃b.rd = _; rw [rd₃b, rd₃a, rd₂]
  have wr₃ : s₃.wr = s₀.wr := by show s₃b.wr = _; rw [wr₃b, wr₃a, wr₂]
  have hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [RegUpd.zf_arithFlags, eax₃, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  -- The groups.
  refine WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, sc₃, fun i hi => by omega, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₃, esp₃, by rw [dp₃]; simp,
      by rw [np₃, Nat.mul_zero, Nat.sub_zero], by omega, sc₃, fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega)]

/-! ## The function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' := by
  have hp' := hp
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE, hR⟩ := hp
  let sched := arg s₀ 0
  let R := (arg s₀ 1).toNat
  let D := arg s₀ 2
  let n := (arg s₀ 3).toNat
  let b := arg s₀ 4
  have hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hrA : (⟨argAddr s₀ 0, 20⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 5,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 5,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 4) hwS (argIn rfl rfl rfl 4 (by decide))
    (by rw [ea_arg rfl]; rfl)
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain ⟨s₂, e₂, z₂, o₂, m₂, rd₂, wr₂⟩ := cmpRounds_ok s₁ (argIn rd₁ wr₁ esp₁ 1 (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  have hz₂ : s₂.zf = some (decide (R = 18)) := by
    rw [z₂, ea_arg esp₁, argR f₁ 1 (by decide), show arg s₀ 1 = BitVec.ofNat 32 R by simp [R],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega) (by decide)]
  have hb₂ : BodyPre s₀ b sched D n s₂ :=
    ⟨by rw [o₂ _ (by decide), b₁], by rw [o₂ _ (by decide), esp₁], by rw [m₂]; exact sv₁, by rw [m₂]; exact f₁,
      by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (sched.setWidth 64) R).getD (permOf dir g i) 0
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n g E)
    (WP.ite (decide (R = 18)) ((eval_e s₂).trans hz₂) (fun h => ?_) (fun h => ?_)) fun s₅ d₅ => ?_)
  · obtain rfl : g = 3 := by simp at h; omega
    exact body_wp dir hp' (.inl rfl) hgR hb₂
  · obtain rfl : g = 4 := by simp at h; omega
    exact body_wp dir hp' (.inr rfl) hgR hb₂
  -- The epilogue.
  obtain ⟨s₆, e₆, rg₆, o₆, m₆, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [d₅.wr]; exact hwS) d₅.base
    d₅.scr.saved
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), d₅.esp]
  · rw [m₆]
    exact d₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRS
      · exact dRD) (by decide)
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) g E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Camellia.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Camellia.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    subst hgR
    exact outF_spec (specDir dir) s₀.mem (sched.setWidth 64) (D.setWidth 64) hR j

end VG.Proof.Camellia.X86
