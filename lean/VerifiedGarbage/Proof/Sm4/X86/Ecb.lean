import VerifiedGarbage.Proof.Sm4.X86.Group
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# SM4 ECB on x86 (32-bit): the whole function

`ecb_wp`: with the working space as an argument (`ecbX86`), `ecb dir`
saves the callee-saved registers, builds the table of round keys in the
order `dir` uses them, keeps the data pointer and the count in their slots,
transforms the blocks a group at a time (`dataLoop_wp`) and restores the
registers.
-/

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- The specification's direction. -/
def specDirX86 : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on x86 with its working space as the fourth argument. -/
def ecbX86 (dir : Dir) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) (specDirX86 dir)
        (Spec.Sm4.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_)
open VG.Proof.Sm4 (DInv blocksAt_of_dinv ecb_eq blockFn specDirX86 ecbX86 crypt_eq quads ofBlock outBlock)

theorem outF_spec (dir : Dir) (m : Mem) (sch : Spec.Sm4.Schedule) (D : Addr) (j : Nat) :
    outF m D (dirKeys dir sch) j =
      blockFn sch (specDirX86 dir) (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  cases dir
  · simp only [outF, blockFn, specDirX86, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · simp only [outF, blockFn, specDirX86, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-! ## The arguments -/

theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
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

/-! ## The function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE⟩ := hp
  let sched := arg s₀ 0
  let D := arg s₀ 1
  let n := (arg s₀ 2).toNat
  let b := arg s₀ 3
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hrK : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  have hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS) (by decide)
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  have subS : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    fun k hk => slot_sub hfit' hk
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 3) hwS (argIn rfl rfl rfl 3 (by decide))
    (by rw [ea_arg rfl]; rfl)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  have hk₁ : SchedPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dKS⟩
  -- The table.
  refine WP.seq (WP.mono (keys_wp dir hk₁ (argIn rd₁ wr₁ esp₁ 0 (by decide))
    (by rw [ea_arg esp₁]; exact argR f₁ 0 (by decide))) fun s₂ k₂ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys dir (Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64))
  have hsch : Spec.Sm4.scheduleAt s₁.mem (sched.setWidth 64) = Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64) :=
    hk₁.sched_eq (Nat.le_refl _) f₁
  have f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₂.mem :=
    f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega)⟩)
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [k₂.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₁]
  have sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · have := k₂.key.keys e he
      rw [base₂, hsch] at this
      exact this
    · rw [← sv₁ i hi]
      exact slot_keep hfit' (lo := tableEnd) (hi := slots) (Nat.le_refl _) k₂.frame
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by rw [tableEnd_eq, slots_eq]; decide))
        (by rw [savedSlot_eq, tableEnd_eq]; omega) (by rw [savedSlot_eq, slots_eq]; omega)
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, wr₁]
  -- The data pointer and the count to their slots.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a, f₃a⟩ := argSlot_ok s₂ (i := 1) (k := dSlot) base₂ (by decide)
    (by rw [wr₂]; exact hwS) (argIn rd₂ wr₂ esp₂ 1 (by decide))
  have f₀₃a : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃a.mem :=
    f₀₂.trans (f₃a.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact subS _ (by decide)⟩)
  have esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b, f₃b⟩ := argSlot_ok s₃a (i := 2) (k := nSlot)
    ((o₃a _ (by decide)).trans base₂) (by decide) (by rw [wr₃a, wr₂]; exact hwS)
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 2 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .eax &&& s₃b.gpr .eax) false false
  have e₃ : runBlock isa [.mov .eax (.mem (argOp 1)), st dSlot .eax, .mov .eax (.mem (argOp 2)), st nSlot .eax,
      .alu .test .eax (.reg .eax)] s₂ = some s₃ := by
    rw [show ([.mov .eax (.mem (argOp 1)), st dSlot .eax, .mov .eax (.mem (argOp 2)), st nSlot .eax,
        .alu .test .eax (.reg .eax)] : List Instr) =
      [.mov .eax (.mem (argOp 1)), .store (slotAt .edi dSlot) .eax] ++
        ([.mov .eax (.mem (argOp 2)), .store (slotAt .edi nSlot) .eax] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_app, e₃a, Option.bind_some, runBlock_app, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have eax₃ : s₃b.gpr .eax = arg s₀ 2 := by
    rw [a₃b, ea_arg esp₃a]; exact argR f₀₃a 2 (by decide)
  have dp₃ : s₃.mem.readW (wordAddr b dSlot) 32 = D := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := dSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_right (by decide),
      m₃a, readW_slot_write hfit' (j := dSlot) (k := dSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ea_arg esp₂]
    exact argR f₀₂ 1 (by decide)
  have np₃ : s₃.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 n := by
    show s₃b.mem.readW _ 32 = _
    rw [m₃b, readW_slot_write hfit' (j := nSlot) (k := nSlot) _ (by decide) (by decide), ite_eq_left rfl,
      ← a₃b, eax₃]
    simp only [n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have f₃ : Frame [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩] s₂.mem s₃.mem :=
    (f₃a.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (f₃b.sub fun r hr => ⟨r, by
        rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  have sc₃ : ScrOk s₀ b E s₃.mem := sc₂.frame hfit' f₃ (dn_disj hfit')
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
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)) fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, sc₃, fun i hi => by omega, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ ⟨base₃, esp₃, by rw [dp₃]; simp,
      by rw [np₃, Nat.mul_zero, Nat.sub_zero], by omega, sc₃, fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega)]
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
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Sm4.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Sm4.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem _ _ j

end VG.Proof.Sm4.X86
