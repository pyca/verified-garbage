import VerifiedGarbage.Proof.Sm4.X86_64.Group

/-!
# One group of blocks of SM4 ECB on x86-64

`dataGroup_wp`: one iteration of the data loop copies the group's blocks to
the tail buffer, transforms them there (`crypt16_wp`), copies them back and
steps to the next group.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)
open VG.Proof.Sm4 (DInv ofInt_nat quads ofBlock outBlock not_contains_off toNat_off blockAt_getD)

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n : Nat} {E : Nat → Spec.Sm4.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa Impl.Sm4.X86_64.group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  rw [slots_eq] at hfit
  let v := n - 16 * k
  let c := min v 16
  have hv : v < 2 ^ 64 := by omega
  have hc0 : 0 < c := by omega
  have hc16 : c ≤ 16 := by omega
  have hkc : 256 * k + 16 * c ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 64 (256 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t, t < 32 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)
  have inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega) (by omega)
  have sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega))
  unfold Impl.Sm4.X86_64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.r8 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .rax .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := slotAddr_ok s₂a .rbx tailSlot (by decide)
  have base₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), o₂a _ (by decide), o₁ _ (by decide), hi.base]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂ r h2, o₂a r h1, o₁ r h3]
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₂a, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copy_wp (X := A) (Y := T) hc0 hc16
    (by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide), hi.rdx])
    (by rw [r₂, o₂a _ (by decide), o₁ _ (by decide), hi.base])
    (by rw [o₂ _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  have g₃' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h2 h3]
  have base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hi.base]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  have sc₃ : ScrOk s₀ b E s₃.mem := by
    refine hi.scr.frame f₃' fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, tableSlot_eq, savedSlot_eq]) <;> omega
  -- The sixteen blocks.
  have hkey : KeyCtx s₃ E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      keys := fun e he => by rw [base₃]; exact sc₃.keys e he }
  have hrdi₃ : s₃.gpr .rdi = s₃.gpr sb + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hi.rdi, base₃]
  refine WP.seq (WP.mono (crypt16_wp hkey (sc₃.masks.ok base₃) hrdi₃) fun s₄ ⟨c₄, b₄⟩ => ?_)
  have base₄ : s₄.gpr sb = b := by rw [c₄.base, base₃]
  have f₄ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₄.mem := by have := c₄.frame; rw [base₃] at this; exact this
  have g₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [c₄.keep r h1 h2, g₃' r (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))
      (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))]
  have sc₄ : ScrOk s₀ b E s₄.mem := by
    refine sc₃.frame2 f₄ (c₄.masks.at base₄) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    subst hr
    rcases ht with rfl | rfl
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]) (by rw [tableSlot_eq]; omega)
    · exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega)
  -- The tail buffer back to the group's blocks.
  have r8₄ : s₄.gpr .r8 = BitVec.ofNat 64 v := by rw [g₄ _ (by decide) (by decide), hi.r8]
  have rdx₄ : s₄.gpr .rdx = A := by rw [g₄ _ (by decide) (by decide), hi.rdx]
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r8₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ => ?_))
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := slotAddr_ok s₅ .rax tailSlot (by decide)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₆a .rbx .rdx
  refine WP.seq (WP.of_runBlock ⟨s₆, by rw [runBlock_app, e₆a, Option.bind_some, e₆], ?_⟩)
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₆a, m₅]
  have wr₄' : s₄.wr = s.wr := by rw [c₄.wr, wr₃']
  have rd₄' : s₄.rd = s.rd := by rw [c₄.rd, rd₃']
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅, wr₄']
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅, rd₄']
  have g₆ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → s₆.gpr r = s₄.gpr r := fun r h1 h2 h3 => by
    rw [o₆ r h2, o₆a r h1, o₅ r h3]
  refine WP.mono (copy_wp (X := T) (Y := A) hc0 hc16
    (by rw [o₆ _ (by decide), r₆a, o₅ _ (by decide), base₄])
    (by rw [r₆, o₆a _ (by decide), o₅ _ (by decide), rdx₄])
    (by rw [o₆ _ (by decide), o₆a _ (by decide), c₅])
    (fun t ht => by rw [rd₆', wr₆']; exact inRd (inT t (by omega)))
    (fun t ht => by rw [wr₆']; exact inA t ht) sepAT.symm) fun s₇ ⟨cp₇, f₇, g₇, rd₇, wr₇⟩ => ?_
  have g₇' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s₇.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 => by rw [g₇ r h1 h2 h3 h4, g₆ r h1 h2 h3]
  have base₇ : s₇.gpr sb = b := by rw [g₇' _ (by decide) (by decide) (by decide) (by decide), base₄]
  have rdx₇ : s₇.gpr .rdx = A := by rw [g₇' _ (by decide) (by decide) (by decide) (by decide), rdx₄]
  have r8₇ : s₇.gpr .r8 = BitVec.ofNat 64 v := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), r8₄]
  have rdi₇ : s₇.gpr .rdi = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide), hi.rdi]
  have rsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide) (by decide), hi.rsp]
  have wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆', hi.wr]
  have rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆', hi.rd]
  -- The scratch buffer and the frame.
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  have sc₇ : ScrOk s₀ b E s₇.mem := by
    refine (mem₆ ▸ sc₄).frame f₇ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [tableSlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega))).sub_right hsub).symm
  have fr₇ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₇.mem := by
    refine ((f₃'.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₄.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₆ ▸ f₇).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega)
  -- The blocks the sixteen-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₃ j = Spec.Sm4.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (16 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add, addr_add]
    have ht : 16 * j + u < 16 * c := by omega
    have := cp₃ (16 * j + u) ht
    rw [addr_add] at this
    rw [show 8 * tailSlot + 16 * j + u = 8 * tailSlot + (16 * j + u) by omega, this, mem₂, addr_add,
      hi.data _ (by omega), ite_eq_right (by omega),
      show 256 * k + (16 * j + u) = 16 * (16 * k + j) + u by omega]
  have hdata : DInv s₀.mem s₇.mem D n (16 * k + c) (outF s₀.mem D E) := by
    intro i hin
    by_cases hin1 : 256 * k ≤ i ∧ i < 256 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 256 * k) := by
        rw [addr_add, show 256 * k + (i - 256 * k) = i by omega]
      rw [e1, cp₇ _ (by omega), mem₆, ite_eq_left (show i < 16 * (16 * k + c) by omega),
        show i / 16 = 16 * k + (i - 256 * k) / 16 by omega, show i % 16 = (i - 256 * k) % 16 by omega]
      have hj : (i - 256 * k) / 16 < c := by omega
      have eT : T + BitVec.ofNat 64 (i - 256 * k) = s₄.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 256 * k) / 16)) +
          BitVec.ofNat 64 ((i - 256 * k) % 16) := by
        rw [base₄, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 256 * k) / 16) + (i - 256 * k) % 16 =
          8 * tailSlot + (i - 256 * k) by omega]
      rw [eT, ← blockAt_getD s₄.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₄ _).getD _ 0 = _
      rw [b₄ _ (by omega), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega) (by omega) (by omega) (by omega)
      have hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₇ _ hout, mem₆,
        f₄.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)) (by simp only; omega) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega))
          (by simp only; omega) hin,
        hi.data i hin]
      by_cases h2 : i < 256 * k
      · rw [ite_eq_left (show i < 16 * (16 * k) by omega), ite_eq_left (show i < 16 * (16 * k + c) by omega)]
      · rw [ite_eq_right (show ¬ i < 16 * (16 * k) by omega), ite_eq_right (show ¬ i < 16 * (16 * k + c) by omega)]
  have fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₇.mem := hi.frame.trans fr₇
  -- On to the next group.
  unfold advance
  obtain ⟨s₈, e₈, cf₈, g₈, m₈, rd₈, wr₈⟩ := cmpImm_ok s₇ .r8 16 r8₇ hv rfl
  refine WP.seq (WP.of_runBlock ⟨s₈, e₈, ?_⟩)
  refine WP.ite (decide (v < 16)) (by simp [X86_64.eval, cf₈]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt' : v < 16 := by simpa using hlt
    obtain ⟨s₉, e₉, z₉, o₉, m₉, rd₉, wr₉⟩ := subSelf_ok s₈ .r8
    refine WP.of_runBlock ⟨s₉, e₉, .inl ⟨z₉, ?_⟩⟩
    have hn : 16 * k + c = n := by omega
    refine ⟨by rw [o₉ _ (by decide), g₈, base₇], by rw [o₉ _ (by decide), g₈, rsp₇],
      by rw [m₉, m₈]; exact sc₇, fun i hi' => by rw [m₉, m₈, hdata i hi', hn], by rw [m₉, m₈]; exact fr,
      by rw [rd₉, rd₈, rd₇'], by rw [wr₉, wr₈, wr₇']⟩
  · have hge' : 16 ≤ v := by simpa using hge
    have hc : c = 16 := by omega
    obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := addImm_ok s₈ .rdx 256
    obtain ⟨s₁₀, e₁₀, r₁₀, z₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subImm_ok s₉ .r8 16
    have r8₉ : s₉.gpr .r8 = BitVec.ofNat 64 v := by rw [o₉ _ (by decide), g₈, r8₇]
    have hz : s₁₀.zf = some (decide (v = 16)) := by
      rw [z₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq hv (by decide)]
    refine WP.of_runBlock ⟨s₁₀, by
      rw [show ([Instr.alu .add .rdx (.imm 256), .alu .sub .r8 (.imm 16)] : List Instr) =
        [.alu .add .rdx (.imm 256)] ++ [.alu .sub .r8 (.imm 16)] from rfl, runBlock_app, e₉,
        Option.bind_some, e₁₀], ?_⟩
    have hm : s₁₀.mem = s₇.mem := by rw [m₁₀, m₉, m₈]
    have base₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, base₇]
    have rsp₁₀ : s₁₀.gpr .rsp = s₀.gpr .rsp := by rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rsp₇]
    have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₇']
    have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₇']
    by_cases h16 : v = 16
    · refine .inl ⟨by rw [hz, h16]; rfl, base₁₀, rsp₁₀, hm ▸ sc₇, ?_, hm ▸ fr, rd₁₀', wr₁₀'⟩
      intro i hi'
      rw [hm, hdata i hi', show 16 * k + c = n by omega]
    · refine .inr ⟨by rw [hz]; simp [h16], base₁₀, rsp₁₀, ?_, ?_, by omega, ?_, hm ▸ sc₇, ?_, hm ▸ fr,
        rd₁₀', wr₁₀'⟩
      · rw [o₁₀ _ (by decide), r₉, g₈, rdx₇, show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl,
          addr_add, show 256 * k + 256 = 256 * (k + 1) by omega]
      · rw [r₁₀, r8₉, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
          VG.Offset.ofNat_sub_ofNat (by omega), show v - 16 = n - 16 * (k + 1) by omega]
      · rw [o₁₀ _ (by decide), o₉ _ (by decide), g₈, rdi₇]
      · intro i hi'
        rw [hm, hdata i hi', show 16 * k + c = 16 * (k + 1) by omega]

end VG.Proof.Sm4.X86_64
