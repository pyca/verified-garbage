import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
import VerifiedGarbage.Proof.Sm4.X86_64.CtrSetup
import VerifiedGarbage.Proof.Sm4.CtrSpec

/-!
# SM4-CTR on x86-64: the whole function

`ctr_wp`: with the working space as an argument (`ctrX86_64`), `ctr` saves
the callee-saved registers, sets the masks, reads the counter block and
writes the one to continue from (`ctrSetup_ok`), builds the table of round
keys, transforms the blocks a group at a time (`ctrGroup_wp`) and restores
the registers. The data loop's invariant is relative to the memory after
the table: the counter block is written by then, and stays.
-/

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- CTR on x86-64 with its working space at `r8`. -/
def ctrX86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let ctr : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [ctr, data, scratch] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      sched.Disjoint scratch ∧ ctr.Disjoint data ∧ ctr.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Ctr.crypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi))) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16)
          (Spec.Cbc.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Ctr.next (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) (s.gpr .rcx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st setMasks)
open VG.Proof.Sm4 (DInv ctrX86_64 crypt_eq quads ofBlock outBlock ctrBlock ctr_of_dinv)
open VG.Spec.Aes (bytesAt)

theorem ctrLoop_wp {s₀ : State} {b D : Addr} {n : Nat} {R : Region} {E : Nat → Spec.Sm4.Word} {V : Nat}
    (hp : GPre s₀ b D n) {s : State} (hi : CInv s₀ b D n R E V 0 s) :
    WP isa (.loop ctrGroup .ne) s (CDone s₀ b D n R E V) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 16 * k ∧ CInv s₀ b D n R E V k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (ctrGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 16 * (k + 1), by have := d.lt; have := hk.lt; omega,
      k + 1, rfl, d⟩

theorem ctrPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .r8 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr) :
    ∃ s, runBlock isa (([movR sb .r8, movR .r8 .rcx] : List Instr) ++ saveRegs ++ setMasks keyMasks) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r8 = s₀.gpr .rcx ∧ (∀ r, r ≠ .r9 → r ≠ .r8 → r ≠ t0 → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ Frame [⟨b, 8 * slots⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .r8
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .r8 .rcx
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), r₁a, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, -, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁, wr₁a]; exact hw) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega)
    (by decide)
  have g₁ : ∀ r, r ≠ .r9 → r ≠ .r8 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [o₁ r h2, o₁a r h1]
  refine ⟨s₃, by
    rw [runBlock_app, runBlock_app, show ([movR sb .r8, movR .r8 .rcx] : List Instr) =
      [movR sb .r8] ++ [movR .r8 .rcx] from rfl, runBlock_app, e₁a, Option.bind_some, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃],
    by rw [g₃ _ (by decide), g₂, hb₁], by rw [g₃ _ (by decide), g₂, r₁, o₁a _ (by decide)],
    fun r h1 h2 h4 => by rw [g₃ r h4, g₂, g₁ r h1 h2], fun i hi => ?_, fun kv hkv => v₃ kv hkv, ?_,
    by rw [rd₃, rd₂, rd₁, rd₁a], by rw [wr₃, wr₂, wr₁, wr₁a]⟩
  · obtain ⟨n1, n2, -⟩ := sreg_ne i
    rw [← g₁ _ n1 n2, ← sv₂ i hi]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  · have hm1 : s₁.mem = s₀.mem := by rw [m₁, m₁a]
    rw [← hm1]
    refine f₂.trans (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)

theorem scheduleAt_congr {m m' : Mem} {p : Addr}
    (hb : ∀ k < 128, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    Spec.Sm4.scheduleAt m' p = Spec.Sm4.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sm4.scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rw [hb (4 * i + 0) (by omega), hb (4 * i + 1) (by omega), hb (4 * i + 2) (by omega), hb (4 * i + 3) (by omega)]

theorem cbcBlocks_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) :
    Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  exact bytesAt_frame hf (fun r hr => (hd r hr).sub_left (VG.Offset.sub_base D (by omega))) (by omega)

theorem ksF_eq (sch : Spec.Sm4.Schedule) (V j : Nat) :
    ksF (dirKeys .encrypt sch) V j = Spec.Sm4.encryptBlock sch (ctrBlock (V + j)) := by
  simp only [ksF, Spec.Sm4.encryptBlock, crypt_eq]; rfl

theorem ctr_wp {s₀ : State} (hp : ctrX86_64.pre s₀) :
    WP isa ctr s₀ fun s' => gprPreserved s₀ s' ∧ ctrX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, dRC, dRD, dRS, fitK, fitC, fitD, fitB⟩ := hp
  let b := s₀.gpr .r8
  let P := s₀.gpr .rsi
  let D := s₀.gpr .rdx
  let n := (s₀.gpr .rcx).toNat
  let sched := s₀.gpr .rdi
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  have hwP : (⟨P, 16⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [P]
  have hrK : (⟨sched, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  have hfitB := fitB
  rw [slots_eq] at hfitB
  unfold ctr
  -- The prologue and the counter block.
  obtain ⟨s₁, e₁, b₁, r8₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := ctrPrologue_ok (b := b) rfl hwS
  have hn₁ : s₁.gpr .r8 = BitVec.ofNat 64 n := by rw [r8₁]; simp [n]
  obtain ⟨s₂, e₂, hi₂, lo₂, bP₂, f₂, g₂, rd₂, wr₂⟩ := ctrSetup_ok s₁ (B := b) (P := P) (N := n)
    (s₀.gpr .rcx).isLt b₁ (by rw [wr₁]; exact hwS) (g₁ _ (by decide) (by decide) (by decide))
    (by rw [wr₁]; exact hwP) dCS hn₁
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  let t := bytesAt s₀.mem P 16
  have ht : t.length = 16 := by simp [t, bytesAt]
  have hV : ctrVal s₁.mem P = Spec.Ctr.toNat t := by
    show Spec.Ctr.toNat (bytesAt s₁.mem P 16) = _
    rw [bytesAt_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dCS) (by decide)]
  rw [hV] at hi₂ lo₂ bP₂
  let V := Spec.Ctr.toNat t
  have subC : Region.Sub (ctrRegion b) ⟨b, 8 * slots⟩ := VG.Offset.sub_base b (by rw [ctrHi_eq, slots_eq])
  have F₂ : Frame [⟨b, 8 * slots⟩, ⟨P, 16⟩] s₀.mem s₂.mem :=
    (f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self,
      fun _ h => h⟩).trans (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, subC⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide) (by decide), b₁]
  have masks₂ : MasksOk s₂ := by
    refine MasksAt.ok (fun kv hkv => ?_) base₂
    rw [f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (m₁.at b₁) kv hkv
    · have := mask_range hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint b (Or.inl (by rw [ctrHi_eq]; omega)) (by omega) (by rw [ctrHi_eq]; omega)
      · exact (dCS.sub_right (slot_sub' (by rw [slots_eq]; omega))).symm
  have hk₂ : SchedPre s₂ b sched :=
    ⟨base₂, by rw [wr₂, wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₂, rd₁]; exact hrK), fitK, dKS⟩
  have rdi₂ : s₂.gpr .rdi = sched := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  -- The table.
  refine WP.seq (WP.mono (keys_wp .encrypt hk₂ rdi₂ masks₂) fun s₃ k₃ => ?_)
  let E : Nat → Spec.Sm4.Word := dirKeys .encrypt (Spec.Sm4.scheduleAt s₀.mem sched)
  have hsch : Spec.Sm4.scheduleAt s₂.mem sched = Spec.Sm4.scheduleAt s₀.mem sched :=
    scheduleAt_congr fun k hk => F₂.bytes (R := ⟨sched, 128⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC) (by show 128 ≤ 2 ^ 64; omega) hk
  have subT : Region.Sub ⟨b, 8 * tableEnd⟩ ⟨b, 8 * slots⟩ :=
    Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega)
  have F₃ : Frame [⟨b, 8 * slots⟩, ⟨P, 16⟩] s₀.mem s₃.mem :=
    F₂.trans (k₃.frame.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩)
  have base₃ : s₃.gpr sb = b := by rw [k₃.pre.base]
  let σ : State := { s₀ with mem := s₃.mem }
  have sc₃ : ScrOk σ b E s₃.mem := by
    refine ⟨k₃.masks.at base₃, fun e he => ?_, fun i hi => ?_⟩
    · have := k₃.key.keys e he
      rw [base₃, hsch] at this
      exact this
    · show _ = s₀.gpr (sreg i)
      rw [← sv₁ i hi]
      have hd : ∀ r ∈ ([⟨b, 8 * tableEnd⟩] : List Region),
          Region.Disjoint ⟨wordAddr b (savedSlot + i), 8⟩ r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega)
          (by rw [savedSlot_eq]; omega)
      rw [k₃.frame.readW (Region.contains_self _ _) hd (by decide)]
      refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint b (Or.inl (by rw [ctrHi_eq, savedSlot_eq]; omega)) (by rw [savedSlot_eq]; omega)
          (by rw [ctrHi_eq]; omega)
      · exact (dCS.sub_right (slot_sub' (by rw [slots_eq, savedSlot_eq]; omega))).symm
  have keepC : ∀ x, x = ctrHi ∨ x = ctrLo → s₃.mem.readW (wordAddr b x) 64 = s₂.mem.readW (wordAddr b x) 64 :=
    fun x hx => k₃.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hx with rfl | rfl <;> exact VG.Offset.disjoint_base b (by rw [tableEnd_eq]; decide) (by decide))
      (by decide)
  have bP₃ : bytesAt s₃.mem P 16 = Spec.Ctr.ofNat (V + n) 16 := by
    rw [← bP₂]
    exact bytesAt_frame k₃.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dCS.sub_right subT) (by decide)
  have data₃ : Spec.Cbc.blocksAt s₃.mem D n = Spec.Cbc.blocksAt s₀.mem D n :=
    cbcBlocks_frame F₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dDS
      · exact dCD.symm)
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [k₃.regs _ (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide)]
  have r8₃ : s₃.gpr .r8 = s₀.gpr .rcx := by
    rw [k₃.regs _ (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide), r8₁]
  have rdx₃ : s₃.gpr .rdx = D := by
    rw [k₃.regs _ (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [k₃.rd, rd₂, rd₁]
  have wr₃ : s₃.wr = s₀.wr := by rw [k₃.wr, wr₂, wr₁]
  -- Any blocks?
  obtain ⟨s₄, e₄, z₄, g₄, m₄, rd₄, wr₄⟩ := testSelf_ok s₃ .r8
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have hz₄ : s₄.zf = some (decide (n = 0)) := by
    rw [z₄, r8₃]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp [n, h], fun h => BitVec.eq_of_toNat_eq (by simpa [n] using h)⟩
  let R : Region := ⟨b, 8 * slots⟩
  refine WP.seq (WP.mono (M := isa) (Q := CDone σ b D n R E V)
    (WP.ite (decide (n = 0)) (by simp [X86_64.eval, hz₄]) (fun h0 => ?_) (fun h0 => ?_)) fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [g₄, base₃], by rw [g₄, rsp₃], by rw [m₄]; exact sc₃, fun i hi => by omega,
      by rw [m₄]; exact Frame.refl _ _, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine ctrLoop_wp (s₀ := σ) ⟨hwS, hwD, dDS, fitB, fitD⟩ ⟨by rw [g₄, base₃], by rw [g₄, rsp₃],
      by rw [g₄, rdx₃]; simp, by rw [g₄, r8₃, Nat.mul_zero, Nat.sub_zero]; simp [n], by omega,
      by rw [g₄, k₃.rdi], by rw [m₄]; exact sc₃, ?_, ?_, fun i hi => ?_, by rw [m₄]; exact Frame.refl _ _,
      by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩
    · rw [m₄, keepC _ (.inl rfl), hi₂, Nat.mul_zero, Nat.add_zero]
    · rw [m₄, keepC _ (.inr rfl), lo₂, Nat.mul_zero, Nat.add_zero]
    · rw [m₄, ite_eq_right (by omega)]
  -- The epilogue.
  obtain ⟨s₆, e₆, rg₆, o₆, f₆, rd₆, wr₆⟩ := restore_ok (by rw [d₅.wr]; exact hwS) d₅.base d₅.scr.saved
  have F₆ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩, R] s₃.mem s₆.mem :=
    d₅.frame.trans (f₆.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩)
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by omega)
    · exact rg₆ 1 (by omega)
    · rw [o₆ _ (fun i hi => by unfold sreg; split <;> decide), d₅.rsp]
    · exact rg₆ 2 (by omega)
    · exact rg₆ 3 (by omega)
    · exact rg₆ 4 (by omega)
    · exact rg₆ 5 (by omega)
  · -- The return address is untouched.
    have fr : Frame [⟨b, 8 * slots⟩, ⟨P, 16⟩, ⟨D, 16 * n⟩] s₀.mem s₆.mem :=
      (F₃.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp).trans
        (F₆.mono fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp [R])
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRS
    · exact dRC
    · exact dRD
  · have hd₆ : DInv s₃.mem s₆.mem D n n (ctrF s₃.mem D E V) := fun i hi => by
      rw [f₆.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dDS.sub_right (Region.sub_prefix (Nat.le_refl _)))
        (by simp only; omega) hi]
      exact d₅.data i hi
    show Spec.Cbc.blocksAt s₆.mem D n = Spec.Ctr.crypt _ t (Spec.Cbc.blocksAt s₀.mem D n)
    rw [← data₃]
    refine ctr_of_dinv _ ht (fun j _ => ?_) hd₆
    have hE : ksF E V j = Spec.Sm4.encryptBlock (Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) (ctrBlock (Spec.Ctr.toNat t + j)) :=
      ksF_eq _ _ _
    simp only [ctrF, hE]
  · show bytesAt s₆.mem P 16 = Spec.Ctr.next t n
    rw [AesCtr.next_eq ht, ← bP₃]
    exact bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dCS
      · exact dCD
      · exact dCS) (by decide)

end VG.Proof.Sm4.X86_64
