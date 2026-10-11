import VerifiedGarbage.Proof.Idea.X86.Invert
import VerifiedGarbage.Proof.Idea.X86.Block

/-!
# IDEA ECB on x86 (32-bit)

`ecb_wp`: with the scratch buffer as an argument (33 words, at `B`), the
code saves `ebx`, `esi`, `edi`, `ebp` in it (`savedSlot`), copies the
subkeys to it (`copy_run`), puts the data pointer and `n` in their slots,
transforms the blocks in a loop (`loop_ok`) whose invariant (`LoopInv`)
says how many remain, that the ones before are transformed and the ones
after not yet (each iteration is `cryptBlockWith_run`), and restores the
registers.
-/

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-! ## Copying the subkeys -/

/-- The bytes of two areas agree if their 32-bit words do. -/
theorem scheduleAt_of_words {m m' : Mem} {S B : Addr}
    (h : ∀ i < 26, m'.readW (B + BitVec.ofNat 64 (4 * i)) 32 = m.readW (S + BitVec.ofNat 64 (4 * i)) 32) :
    Spec.Idea.scheduleAt m' B = Spec.Idea.scheduleAt m S := by
  have hb : ∀ j < 104, m' (B + BitVec.ofNat 64 j) = m (S + BitVec.ofNat 64 j) := by
    intro j hj
    have e : ∀ p : Addr, p + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (4 * (j / 4)) + BitVec.ofNat 64 (j % 4) :=
      fun p => by rw [Offset.add_ofNat_add_ofNat]; congr 2; omega
    rw [e B, e S, Mem.readW_byte m' _ (Nat.mod_lt j (by decide)), Mem.readW_byte m _ (Nat.mod_lt j (by decide)),
      h _ (by omega)]
  apply Vector.ext
  intro i hi
  simp only [Spec.Idea.scheduleAt, Vector.getElem_ofFn]
  rw [hb _ (by omega), hb _ (by omega)]

/-- After `k` words of the copy from `edx` to `esi`. -/
structure CopyInv (s₀ : State) (k : Nat) (t : State) : Prop where
  keep : Keep [.eax] { s₀ with mem := t.mem } t
  frame : Frame [⟨(s₀.gpr .esi).setWidth 64, 4 * k⟩] s₀.mem t.mem
  words : ∀ i < k, t.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
    s₀.mem.readW ((s₀.gpr .edx).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32

/-- What the copy needs: the subkeys (104 bytes at `edx`) readable, the
copy (at `esi`, in a region of `n` bytes) writable, apart, neither wrapping
around. -/
structure CopyPre (n : Nat) (s : State) : Prop where
  src : ⟨(s.gpr .edx).setWidth 64, 104⟩ ∈ s.rd ++ s.wr
  dst : ⟨(s.gpr .esi).setWidth 64, n⟩ ∈ s.wr
  len : 104 ≤ n
  sep : Region.Disjoint ⟨(s.gpr .edx).setWidth 64, 104⟩ ⟨(s.gpr .esi).setWidth 64, n⟩
  fitS : (s.gpr .edx).toNat + 104 ≤ 2 ^ 32
  fitB : (s.gpr .esi).toNat + n ≤ 2 ^ 32

theorem copy_run {n : Nat} (s₀ : State) (hp : CopyPre n s₀) : ∀ k ≤ 26, ∃ t,
    runBlock isa ((List.range k).flatMap copyWord) s₀ = some t ∧ CopyInv s₀ k t
  | 0, _ => ⟨s₀, by simp [runBlock_nil], ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩⟩
  | k + 1, hk => by
    obtain ⟨t, ht, hi⟩ := copy_run s₀ hp k (by omega)
    have := hp.len; have := hp.fitS; have := hp.fitB
    have edx : t.gpr .edx = s₀.gpr .edx := hi.keep.reg .edx (by decide)
    have esi : t.gpr .esi = s₀.gpr .esi := hi.keep.reg .esi (by decide)
    have hsrc : InRegions (t.rd ++ t.wr) (addr (t.gpr .edx) (4 * k)) 4 := by
      rw [edx, hi.keep.rd, hi.keep.wr, addr_eq (by omega)]
      exact ⟨_, hp.src, Offset.contains_base _ (by omega) (by omega)⟩
    obtain ⟨t₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ t (load_src hsrc)
    have hdst : InRegions t₁.wr (addr (t₁.gpr .esi) (4 * k)) 4 := by
      rw [e₁.reg .esi (by decide), esi, e₁.wr, hi.keep.wr, addr_eq (by omega)]
      exact ⟨_, hp.dst, Offset.contains_base _ (by omega) (by omega)⟩
    obtain ⟨t₂, h₂, m₂, g₂, rd₂, wr₂⟩ := store_run .esi .eax (4 * k) t₁ hdst
    have esi₁ : t₁.gpr .esi = s₀.gpr .esi := (e₁.reg .esi (by decide)).trans esi
    have aB : addr (s₀.gpr .esi) (4 * k) = (s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
      addr_eq (by omega)
    refine ⟨t₂, ?_, ⟨⟨fun r hr => ?_, rfl, ?_, ?_⟩, ?_, fun i hik => ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append ht (run_append (a := [_]) h₁ h₂)
    · rw [g₂, e₁.reg r hr]; exact hi.keep.reg r hr
    · rw [rd₂, e₁.rd]; exact hi.keep.rd
    · rw [wr₂, e₁.wr]; exact hi.keep.wr
    · rw [m₂, e₁.mem, esi₁, aB]
      refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega)
    · rw [m₂, e₁.mem, esi₁, aB]
      by_cases he : i = k
      · subst he
        rw [Mem.readW_writeW_self32, v₁, edx, addr_eq (by omega)]
        refine hi.frame.readW (r := ⟨(s₀.gpr .edx).setWidth 64, 104⟩)
          (Offset.contains_base _ (d := 4 * i) (by omega) (by omega)) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.sep.sub_right (Region.sub_prefix (by omega))
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hi.words i (by omega)

/-! ## The contract -/

/-- ECB on x86 with its scratch buffer (`4 * slots` bytes) as the fourth argument. -/
def ecbContract : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 104⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 104 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    Spec.Idea.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64))
        (Spec.Idea.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `ecbContract.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 104⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * slots⟩]
  dSD : Region.Disjoint ⟨(arg s 0).setWidth 64, 104⟩ ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
  dSB : Region.Disjoint ⟨(arg s 0).setWidth 64, 104⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  dDB : Region.Disjoint ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  aD : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
  aB : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  rD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 4 * slots⟩
  fS : (arg s 0).toNat + 104 ≤ 2 ^ 32
  fD : (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 4 * slots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem EPre.of {s : State} (h : ecbContract.pre s) : EPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The callee-saved register saved at word `j` of `savedSlot`. -/
def sreg (j : Nat) : Reg := [Reg.ebx, .esi, .edi, .ebp].getD j .ebx

/-! ## The prologue -/

/-- What the prologue leaves (the scratch buffer at `B`). -/
structure PInv (s p : State) : Prop where
  esi : p.gpr .esi = arg s 3
  esp : p.gpr .esp = s.gpr .esp
  rd : p.rd = s.rd
  wr : p.wr = s.wr
  frame : Frame [⟨(arg s 3).setWidth 64, 4 * slots⟩] s.mem p.mem
  sched : Spec.Idea.scheduleAt p.mem ((arg s 3).setWidth 64) =
    Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)
  data : p.mem.readW ((arg s 3).setWidth 64 + BitVec.ofNat 64 dataSlot) 32 = arg s 1
  left : p.mem.readW ((arg s 3).setWidth 64 + BitVec.ofNat 64 leftSlot) 32 = arg s 2
  saved : ∀ j < 4, p.mem.readW ((arg s 3).setWidth 64 + BitVec.ofNat 64 (savedSlot + 4 * j)) 32 = s.gpr (sreg j)
  zf : p.zf = some (arg s 2 - 0 == 0)

theorem cmp0_run (r : Reg) (s : State) :
    ∃ s', runBlock isa [.alu .cmp r (.imm 0)] s = some s' ∧ s'.zf = some (s.gpr r - 0 == 0) ∧
      Keep [] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-- A word of the scratch buffer, after writes to other words. -/
theorem scr_sep {m : Mem} {B : Addr} {a d : Nat} {v : BitVec 32} (h : a + 4 ≤ d ∨ d + 4 ≤ a)
    (ha : a + 4 ≤ 4 * slots) (hd : d + 4 ≤ 4 * slots) :
    (m.writeW (B + BitVec.ofNat 64 d) v).readW (B + BitVec.ofNat 64 a) 32 = m.readW (B + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by simp only [slots] at ha; omega)
    (by simp only [slots] at hd; omega)) (by decide)

theorem prologue_run (s : State) (hp : EPre s) : ∃ p, runBlock isa prologue s = some p ∧ PInv s p := by
  have fB := hp.fB; have fSp := hp.fSp
  simp only [slots] at fB
  have hargs : ⟨argAddr s 0, 16⟩ ∈ s.rd := by rw [hp.rd]; simp
  let B : Addr := (arg s 3).setWidth 64
  have hBin : ∀ t : State, t.wr = s.wr → ∀ d, d + 4 ≤ 4 * slots → InRegions t.wr (B + BitVec.ofNat 64 d) 4 :=
    fun t ht d hd => by
      rw [ht, hp.wr]
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.contains_base _ hd
        (by simp only [slots] at hd; omega)⟩
  have hBa : ∀ x : BitVec 32, x = arg s 3 → ∀ d, d + 4 ≤ 4 * slots → addr x d = B + BitVec.ofNat 64 d :=
    fun x hx d hd => by rw [hx, addr_eq (by simp only [slots] at hd; omega)]
  -- Saving the registers.
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (arg_src (i := 3) (by decide) hargs (by omega))
  obtain ⟨s₂, h₂, m₂, g₂, rd₂, wr₂⟩ := store_run .eax .ebx (savedSlot + 0) s₁
    (by rw [hBa _ v₁ _ (by decide)]; exact hBin _ e₁.wr _ (by decide))
  obtain ⟨s₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store_run .eax .esi (savedSlot + 4) s₂
    (by rw [g₂, hBa _ v₁ _ (by decide)]; exact hBin _ (by rw [wr₂, e₁.wr]) _ (by decide))
  obtain ⟨s₄, h₄, m₄, g₄, rd₄, wr₄⟩ := store_run .eax .edi (savedSlot + 8) s₃
    (by rw [g₃, g₂, hBa _ v₁ _ (by decide)]; exact hBin _ (by rw [wr₃, wr₂, e₁.wr]) _ (by decide))
  obtain ⟨s₅, h₅, m₅, g₅, rd₅, wr₅⟩ := store_run .eax .ebp (savedSlot + 12) s₄
    (by rw [g₄, g₃, g₂, hBa _ v₁ _ (by decide)]; exact hBin _ (by rw [wr₄, wr₃, wr₂, e₁.wr]) _ (by decide))
  have g₁₅ : s₅.gpr = s₁.gpr := by rw [g₅, g₄, g₃, g₂]
  have g1 : ∀ q, q ≠ .eax → s₁.gpr q = s.gpr q := fun q hq => e₁.reg q (by simpa using hq)
  have m₁₅ : s₅.mem = (((s.mem.writeW (B + BitVec.ofNat 64 (savedSlot + 0)) (s.gpr .ebx)).writeW
      (B + BitVec.ofNat 64 (savedSlot + 4)) (s.gpr .esi)).writeW (B + BitVec.ofNat 64 (savedSlot + 8))
      (s.gpr .edi)).writeW (B + BitVec.ofNat 64 (savedSlot + 12)) (s.gpr .ebp) := by
    rw [m₅, m₄, m₃, m₂, e₁.mem, g₄, g₃, g₂, hBa _ v₁ _ (by decide), hBa _ v₁ _ (by decide),
      hBa _ v₁ _ (by decide), hBa _ v₁ _ (by decide), g1 _ (by decide), g1 _ (by decide), g1 _ (by decide),
      g1 _ (by decide)]
  have f₅ : Frame [⟨B, 4 * slots⟩] s.mem s₅.mem := by
    rw [m₁₅]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have saved₅ : ∀ j < 4, s₅.mem.readW (B + BitVec.ofNat 64 (savedSlot + 4 * j)) 32 = s.gpr (sreg j) := by
    intro j hj
    rw [m₁₅]
    obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · rw [scr_sep (by simp only [savedSlot]; omega) (by decide) (by decide),
        scr_sep (by simp only [savedSlot]; omega) (by decide) (by decide),
        scr_sep (by simp only [savedSlot]; omega) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [scr_sep (by simp only [savedSlot]; omega) (by decide) (by decide),
        scr_sep (by simp only [savedSlot]; omega) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [scr_sep (by simp only [savedSlot]; omega) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [Mem.readW_writeW_self32]; rfl
  have esp₅ : s₅.gpr .esp = s.gpr .esp := by rw [g₁₅, g1 _ (by decide)]
  have rd₁₅ : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, e₁.rd]
  have wr₁₅ : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, e₁.wr]
  have argE : ∀ (t : State) (rs : List Region), Frame rs s.mem t.mem →
      (∀ r ∈ rs, Region.Disjoint ⟨argAddr s 0, 16⟩ r) → t.gpr .esp = s.gpr .esp → ∀ i, i < 4 →
      arg t i = arg s i := fun t rs hf hd he i hi => arg_frame hf hd he (by omega) (by omega)
  have dAB : ∀ r ∈ [(⟨B, 4 * slots⟩ : Region)], Region.Disjoint ⟨argAddr s 0, 16⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aB
  have hargsT : ∀ t : State, t.rd = s.rd → t.gpr .esp = s.gpr .esp → ⟨argAddr t 0, 16⟩ ∈ t.rd :=
    fun t hr he => by rw [hr]; simp only [argAddr, he]; exact hargs
  -- The subkeys.
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .esi (.reg .eax) _ s₅ rfl
  obtain ⟨s₇, h₇, v₇, e₇⟩ := mov_run .edx _ _ s₆ (arg_src (i := 0) (by decide)
    (hargsT s₆ (by rw [e₆.rd, rd₁₅]) (by rw [e₆.reg .esp (by decide), esp₅])) (by rw [e₆.reg .esp (by decide), esp₅]; omega))
  have mem₇ : s₇.mem = s₅.mem := by rw [e₇.mem, e₆.mem]
  have esi₇ : s₇.gpr .esi = arg s 3 := by rw [e₇.reg .esi (by decide), v₆, g₁₅, v₁]
  have edx₇ : s₇.gpr .edx = arg s 0 := by
    rw [v₇, show arg s₆ 0 = arg s₅ 0 by simp only [arg, argAddr, e₆.mem, e₆.reg .esp (by decide)]]
    exact argE s₅ _ f₅ dAB esp₅ 0 (by decide)
  have esp₇ : s₇.gpr .esp = s.gpr .esp := by rw [e₇.reg .esp (by decide), e₆.reg .esp (by decide), esp₅]
  have rd₇ : s₇.rd = s.rd := by rw [e₇.rd, e₆.rd, rd₁₅]
  have wr₇ : s₇.wr = s.wr := by rw [e₇.wr, e₆.wr, wr₁₅]
  have cp : CopyPre (4 * slots) s₇ := by
    refine ⟨by rw [edx₇, rd₇, hp.rd]; simp, by rw [esi₇, wr₇, hp.wr]; simp, by decide,
      by rw [edx₇, esi₇]; exact hp.dSB, by rw [edx₇]; exact hp.fS, by rw [esi₇]; simp only [slots]; omega⟩
  obtain ⟨s₈, h₈, ci⟩ := copy_run s₇ cp 26 (by decide)
  have esp₈ : s₈.gpr .esp = s.gpr .esp := (ci.keep.reg .esp (by decide)).trans esp₇
  have esi₈ : s₈.gpr .esi = arg s 3 := (ci.keep.reg .esi (by decide)).trans esi₇
  have rd₈ : s₈.rd = s.rd := ci.keep.rd.trans rd₇
  have wr₈ : s₈.wr = s.wr := ci.keep.wr.trans wr₇
  have f₈ : Frame [⟨B, 4 * slots⟩] s.mem s₈.mem := by
    refine f₅.trans ?_
    rw [← mem₇]
    refine ci.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [esi₇]; exact Region.sub_prefix (by decide)
  -- The slots.
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mov_run .eax _ _ s₈ (arg_src (i := 1) (by decide) (hargsT s₈ rd₈ esp₈)
    (by rw [esp₈]; omega))
  obtain ⟨s₁₀, h₁₀, m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := store_run .esi .eax dataSlot s₉
    (by rw [e₉.reg .esi (by decide), hBa _ esi₈ _ (by decide)]; exact hBin _ (by rw [e₉.wr, wr₈]) _ (by decide))
  have esp₁₀ : s₁₀.gpr .esp = s.gpr .esp := by rw [g₁₀, e₉.reg .esp (by decide), esp₈]
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mov_run .eax _ _ s₁₀ (arg_src (i := 2) (by decide)
    (hargsT s₁₀ (by rw [rd₁₀, e₉.rd, rd₈]) esp₁₀) (by rw [esp₁₀]; omega))
  obtain ⟨s₁₂, h₁₂, m₁₂, g₁₂, rd₁₂, wr₁₂⟩ := store_run .esi .eax leftSlot s₁₁
    (by rw [e₁₁.reg .esi (by decide), g₁₀, e₉.reg .esi (by decide), hBa _ esi₈ _ (by decide)]
        exact hBin _ (by rw [e₁₁.wr, wr₁₀, e₉.wr, wr₈]) _ (by decide))
  obtain ⟨s₁₃, h₁₃, z₁₃, e₁₃⟩ := cmp0_run .eax s₁₂
  have a1 : s₉.gpr .eax = arg s 1 := by
    rw [v₉]; exact argE s₈ _ f₈ dAB esp₈ 1 (by decide)
  have mem₁₀ : s₁₀.mem = s₈.mem.writeW (B + BitVec.ofNat 64 dataSlot) (arg s 1) := by
    rw [m₁₀, e₉.mem, e₉.reg .esi (by decide), esi₈, a1, hBa _ rfl _ (by decide)]
  have f₁₀ : Frame [⟨B, 4 * slots⟩] s.mem s₁₀.mem := by
    rw [mem₁₀]; exact f₈.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have a2 : s₁₁.gpr .eax = arg s 2 := by
    rw [v₁₁]; exact argE s₁₀ _ f₁₀ dAB esp₁₀ 2 (by decide)
  have mem₁₂ : s₁₂.mem = s₁₀.mem.writeW (B + BitVec.ofNat 64 leftSlot) (arg s 2) := by
    rw [m₁₂, e₁₁.mem, e₁₁.reg .esi (by decide), g₁₀, e₉.reg .esi (by decide), esi₈, a2,
      hBa _ rfl _ (by decide)]
  refine ⟨s₁₃, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold prologue
    exact run_append (run_append (run_append (run_append h₁ (run_append (a := [_]) h₂ (run_append (a := [_]) h₃
      (run_append (a := [_]) h₄ h₅)))) (run_append (a := [_]) h₆ h₇)) h₈)
      (run_append (a := [_]) h₉ (run_append (a := [_]) h₁₀ (run_append (a := [_]) h₁₁
        (run_append (a := [_]) h₁₂ h₁₃))))
  · rw [e₁₃.reg .esi (by decide), g₁₂, e₁₁.reg .esi (by decide), g₁₀, e₉.reg .esi (by decide), esi₈]
  · rw [e₁₃.reg .esp (by decide), g₁₂, e₁₁.reg .esp (by decide), esp₁₀]
  · rw [e₁₃.rd, rd₁₂, e₁₁.rd, rd₁₀, e₉.rd, rd₈]
  · rw [e₁₃.wr, wr₁₂, e₁₁.wr, wr₁₀, e₉.wr, wr₈]
  · rw [e₁₃.mem, mem₁₂]; exact f₁₀.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  · rw [e₁₃.mem, mem₁₂, mem₁₀]
    refine scheduleAt_of_words fun i hi => ?_
    rw [scr_sep (by simp only [leftSlot]; omega) (by simp only [slots]; omega) (by decide),
      scr_sep (by simp only [dataSlot]; omega) (by simp only [slots]; omega) (by decide)]
    have w := ci.words i hi
    rw [esi₇, edx₇, mem₇] at w
    rw [w]
    refine f₅.readW (r := ⟨(arg s 0).setWidth 64, 104⟩) (Offset.contains_base _ (d := 4 * i) (by omega)
      (by omega)) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.dSB
  · rw [e₁₃.mem, mem₁₂, scr_sep (by simp only [leftSlot, dataSlot]; omega) (by decide) (by decide), mem₁₀,
      Mem.readW_writeW_self32]
  · rw [e₁₃.mem, mem₁₂, Mem.readW_writeW_self32]
  · intro j hj
    rw [e₁₃.mem, mem₁₂, scr_sep (by simp only [leftSlot, savedSlot]; omega)
      (by simp only [slots, savedSlot]; omega) (by decide), mem₁₀,
      scr_sep (by simp only [dataSlot, savedSlot]; omega) (by simp only [slots, savedSlot]; omega) (by decide)]
    rw [← saved₅ j hj, ← mem₇]
    refine ci.frame.readW (r := ⟨B + BitVec.ofNat 64 (savedSlot + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [esi₇]
    exact Offset.disjoint_base _ (by simp only [savedSlot]; omega) (by simp only [savedSlot]; omega)
  · rw [z₁₃, g₁₂, a2]

/-! ## The loop -/

theorem store_zf (b r : Reg) (d : Nat) (s s' : State) (h : runBlock isa [.store (at_ b d) r] s = some s') :
    s'.zf = s.zf := by
  simp only [runBlock_cons, isa, exec, State.store32] at h
  split at h
  · rw [runStep_some, runBlock_nil, Option.some.injEq] at h; subst h; rfl
  · cases h

/-- The facts about the state `o` before the loop that the loop relies on. -/
structure LCtx (z : Spec.Idea.Schedule) (P₀ : BitVec 32) (n : Nat) (o : State) : Prop where
  key : KeyOk z o
  data : ⟨P₀.setWidth 64, 8 * n⟩ ∈ o.wr
  sep : Region.Disjoint ⟨P₀.setWidth 64, 8 * n⟩ ⟨(o.gpr .esi).setWidth 64, 4 * slots⟩
  fit : P₀.toNat + 8 * n ≤ 2 ^ 32

/-- The slots that the loop writes: `t₀`'s, the data pointer's and the count's. -/
abbrev slotsR (o : State) : Region := ⟨(o.gpr .esi).setWidth 64 + BitVec.ofNat 64 t0Slot, 12⟩

/-- `r` blocks remain, from block `n - r` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (P₀ : BitVec 32) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  esi : t.gpr .esi = o.gpr .esi
  esp : t.gpr .esp = o.gpr .esp
  rd : t.rd = o.rd
  wr : t.wr = o.wr
  frame : Frame [⟨P₀.setWidth 64, 8 * n⟩, slotsR o] o.mem t.mem
  data : t.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 dataSlot) 32 = P₀ + BitVec.ofNat 32 (8 * (n - r))
  left : t.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 leftSlot) 32 = BitVec.ofNat 32 r
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j))

/-- After the loop (or none): every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (P₀ : BitVec 32) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  esi : t.gpr .esi = o.gpr .esi
  esp : t.gpr .esp = o.gpr .esp
  rd : t.rd = o.rd
  wr : t.wr = o.wr
  frame : Frame [⟨P₀.setWidth 64, 8 * n⟩, slotsR o] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)))

theorem step_ok {z : Spec.Idea.Schedule} {P₀ : BitVec 32} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LCtx z P₀ n o) (r : Nat) (t : State) (hi : LoopInv z P₀ n m₀ o r t) :
    WP isa (.block ecbBody) t
      (fun t' => (isa.eval .ne t' = some false ∧ LoopPost z P₀ n m₀ o t') ∨
        (isa.eval .ne t' = some true ∧ ∃ r' < r, LoopInv z P₀ n m₀ o r' t')) := by
  have hfB := hc.key.fit
  simp only [slots] at hfB
  have hfD := hc.fit
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega
  have hb64 : 8 * n ≤ 2 ^ 64 := by omega
  let Bs : Addr := (o.gpr .esi).setWidth 64
  let A : Addr := P₀.setWidth 64
  have hBs : ∀ d, d + 4 ≤ 4 * slots → addr (t.gpr .esi) d = Bs + BitVec.ofNat 64 d := fun d hd => by
    rw [hi.esi, addr_eq (by simp only [slots] at hd; omega)]
  -- The subkeys and the slots, outside what the loop writes.
  have dS : ∀ q ∈ [(⟨A, 8 * n⟩ : Region), slotsR o], Region.Disjoint ⟨Bs, 104⟩ q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (hc.sep.symm).sub_left (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint _ (by decide) (by simp only [t0Slot]; omega)
  have hk : KeyOk z t := by
    refine ⟨by rw [hi.esi, hi.wr]; exact hc.key.wr, by rw [hi.esi]; exact hc.key.fit, ?_⟩
    rw [hi.esi, ← hc.key.sched]
    exact scheduleAt_congr (frame_bytes hi.frame dS (by decide))
  -- The block.
  have hP : (P₀ + BitVec.ofNat 32 (8 * (n - r))).setWidth 64 = A + BitVec.ofNat 64 (8 * (n - r)) := by
    rw [← addr_eq (by omega)]; rfl
  have hPfit : (P₀ + BitVec.ofNat 32 (8 * (n - r))).toNat + 8 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * (n - r)) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hin : ∀ i, i + 4 ≤ 8 → InRegions t.wr (A + BitVec.ofNat 64 (8 * (n - r)) + BitVec.ofNat 64 i) 4 :=
    fun i hi' => ⟨_, by rw [hi.wr]; exact hc.data, block_contains hj hi' (by decide) hb64⟩
  have hat : BlockAt z (P₀ + BitVec.ofNat 32 (8 * (n - r))) (A + BitVec.ofNat 64 (8 * (n - r))) t := by
    refine ⟨hk, ?_, hP, hPfit, ?_, ?_⟩
    · rw [hBs _ (by decide)]; exact hi.data
    · have := hin 0 (by decide); rw [BitVec.add_zero] at this
      obtain ⟨R, hR, hc'⟩ := this; exact ⟨R, List.mem_append_right _ hR, hc'⟩
    · obtain ⟨R, hR, hc'⟩ := hin 4 (by decide); exact ⟨R, List.mem_append_right _ hR, hc'⟩
  have hw0 : InRegions t.wr (A + BitVec.ofNat 64 (8 * (n - r))) 4 := by
    have := hin 0 (by decide); rwa [BitVec.add_zero] at this
  have hpre : ∀ u : State, u.gpr .esi = t.gpr .esi → u.rd = t.rd → u.wr = t.wr →
      Frame [⟨addr (t.gpr .esi) t0Slot, 4⟩] t.mem u.mem →
      ∃ u', runBlock isa [.mov .edx (.mem (at_ .esi leftSlot))] u = some u' ∧ Keep [.edx] u u' ∧
        u'.gpr .edx = BitVec.ofNat 32 r := fun u he hr hw hf => by
    have hku : KeyOk z u := ⟨by rw [he, hw]; exact hk.wr, by rw [he]; exact hk.fit, by
      rw [he, ← hk.sched]
      refine scheduleAt_congr (frame_bytes hf (fun q hq => ?_) (by decide))
      simp only [List.mem_singleton] at hq; subst hq
      rw [hBs _ (by decide), hi.esi]
      exact Offset.base_disjoint _ (by decide) (by simp only [t0Slot]; omega)⟩
    obtain ⟨u', h', v', e'⟩ := mov_run .edx _ _ u (slot_src hku (d := leftSlot) (by decide))
    refine ⟨u', h', e', ?_⟩
    rw [v', he, hBs _ (by decide), ← hi.left]
    refine hf.readW (r := ⟨Bs + BitVec.ofNat 64 leftSlot, 4⟩) (Region.contains_self _ _) (fun q hq => ?_)
      (by decide)
    simp only [List.mem_singleton] at hq; subst hq
    rw [hBs _ (by decide)]
    exact Offset.disjoint _ (by simp only [leftSlot, t0Slot]; omega) (by simp only [leftSlot]; omega)
      (by simp only [t0Slot]; omega)
  obtain ⟨t₁, h₁, b₁, f₁, eax₁, esi₁, esp₁, rd₁, wr₁, edx₁⟩ :=
    cryptBlockWith_run z _ (fun v => v = BitVec.ofNat 32 r) t hat hw0 (hin 4 (by decide)) hpre
  -- The next block's address and the count, to their slots.
  have hk₁ : KeyOk z t₁ := ⟨by rw [esi₁, wr₁]; exact hk.wr, by rw [esi₁]; exact hk.fit, by
    rw [esi₁, ← hk.sched]
    refine scheduleAt_congr (frame_bytes f₁ (fun q hq => ?_) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [hi.esi]; exact (hc.sep.symm).sub_left (Region.sub_prefix (by decide)) |>.sub_right
        (Offset.sub_base _ (by omega))
    · rw [hBs _ (by decide), hi.esi]
      exact Offset.base_disjoint _ (by decide) (by simp only [t0Slot]; omega)⟩
  obtain ⟨t₂, h₂, v₂, e₂⟩ := alu_run .add (by simp) .eax (.imm 8) 8 t₁ rfl
  obtain ⟨t₃, h₃, m₃, g₃, rd₃, wr₃⟩ := store_run .esi .eax dataSlot t₂
    (by rw [e₂.reg .esi (by decide), e₂.wr]; exact hk₁.slot (by decide))
  obtain ⟨t₄, h₄, v₄, z₄, e₄⟩ := sub1_run .edx t₃
  obtain ⟨t₅, h₅, m₅, g₅, rd₅, wr₅⟩ := store_run .esi .edx leftSlot t₄
    (by rw [e₄.reg .esi (by decide), g₃, e₂.reg .esi (by decide), e₄.wr, wr₃, e₂.wr]; exact hk₁.slot (by decide))
  have zf₅ : t₅.zf = some (BitVec.ofNat 32 r - 1 == 0) := by
    rw [store_zf _ _ _ _ _ h₅, z₄, g₃, e₂.reg .edx (by decide), edx₁]
  refine WP.of_runBlock ⟨t₅, ?_, ?_⟩
  · exact run_append h₁ (run_append (a := [_]) h₂ (run_append (a := [_]) h₃ (run_append (a := [_]) h₄ h₅)))
  have esi₅ : t₅.gpr .esi = o.gpr .esi := by
    rw [g₅, e₄.reg .esi (by decide), g₃, e₂.reg .esi (by decide), esi₁, hi.esi]
  have esp₅ : t₅.gpr .esp = o.gpr .esp := by
    rw [g₅, e₄.reg .esp (by decide), g₃, e₂.reg .esp (by decide), esp₁, hi.esp]
  have rd₅ : t₅.rd = o.rd := by rw [rd₅, e₄.rd, rd₃, e₂.rd, rd₁, hi.rd]
  have wr₅ : t₅.wr = o.wr := by rw [wr₅, e₄.wr, wr₃, e₂.wr, wr₁, hi.wr]
  have esiB : ∀ d, d + 4 ≤ 4 * slots → addr (t₄.gpr .esi) d = Bs + BitVec.ofNat 64 d := fun d hd => by
    rw [e₄.reg .esi (by decide), g₃, e₂.reg .esi (by decide), esi₁]; exact hBs d hd
  have mem₅ : t₅.mem = (t₁.mem.writeW (Bs + BitVec.ofNat 64 dataSlot)
      (P₀ + BitVec.ofNat 32 (8 * (n - r)) + 8)).writeW (Bs + BitVec.ofNat 64 leftSlot)
      (BitVec.ofNat 32 r - 1) := by
    rw [m₅, e₄.mem, m₃, e₂.mem, v₄, g₃, e₂.reg .edx (by decide), edx₁, esiB _ (by decide)]
    rw [show addr (t₂.gpr .esi) dataSlot = addr (t₄.gpr .esi) dataSlot by
      rw [e₄.reg .esi (by decide), g₃], esiB _ (by decide), v₂, eax₁]
    rfl
  have sl : ∀ d, t0Slot ≤ d → d + 4 ≤ t0Slot + 12 → (slotsR o).Contains (Bs + BitVec.ofNat 64 d) 4 :=
    fun d h₁ h₂ => Offset.contains _ h₁ h₂ (by simp only [t0Slot]; omega)
  have dataSep : ∀ d, t0Slot ≤ d → d + 4 ≤ t0Slot + 12 → ∀ j < n,
      Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * j), 8⟩ ⟨Bs + BitVec.ofNat 64 d, 4⟩ := fun d h₁ h₂ j hj =>
    (hc.sep.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Offset.sub_base _ (by simp only [t0Slot, slots] at *; omega))
  have F₅ : Frame [⟨A + BitVec.ofNat 64 (8 * (n - r)), 8⟩, slotsR o] t.mem t₅.mem := by
    rw [mem₅]
    refine ((f₁.sub fun q hq => ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (sl _ (by decide) (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (sl _ (by decide) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      rw [hBs _ (by decide)]
      exact Offset.sub _ (Nat.le_refl _) (by decide)
  have frame₅ : Frame [⟨A, 8 * n⟩, slotsR o] o.mem t₅.mem :=
    hi.frame.trans (F₅.sub fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩)
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₅.mem (A + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (A + BitVec.ofNat 64 (8 * j)) := by
    refine blockAt_congr (frame_bytes F₅ (fun q hq => ?_) (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact blocks_disjoint hj hjn (Ne.symm hne) hb64
    · exact (hc.sep.sub_left (r₁' := ⟨A + BitVec.ofNat 64 (8 * j), 8⟩) (Offset.sub_base _ (by omega))).sub_right
        (r₂' := slotsR o) (Offset.sub_base _ (by decide))
  have done₅ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₅.mem (A + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (A + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      have hb₅ : Spec.Idea.blockAt t₅.mem (A + BitVec.ofNat 64 (8 * (n - r))) =
          Spec.Idea.blockAt t₁.mem (A + BitVec.ofNat 64 (8 * (n - r))) := by
        have F : Frame [slotsR o] t₁.mem t₅.mem := by
          rw [mem₅]
          exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sl _ (by decide) (by decide))).writeW
            (List.mem_singleton_self _) _ (sl _ (by decide) (by decide))
        refine blockAt_congr (frame_bytes F (fun q hq => ?_) (by decide))
        simp only [List.mem_singleton] at hq; subst hq
        exact (hc.sep.sub_left (r₁' := ⟨A + BitVec.ofNat 64 (8 * (n - r)), 8⟩)
          (Offset.sub_base _ (by omega))).sub_right (r₂' := slotsR o) (Offset.sub_base _ (by decide))
      rw [hb₅, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega) he]
      exact hi.done j (by have := hi.pos; omega)
  have hn32 : n < 2 ^ 32 := by omega
  have hev : isa.eval .ne t₅ = some (decide (r - 1 ≠ 0)) := by
    show t₅.zf.map (!·) = _
    rw [zf₅, Option.map_some]
    congr 1
    have := hi.le; have := hi.pos
    by_cases h0 : r - 1 = 0
    · rw [show r = 1 by omega]; rfl
    · have hne : BitVec.ofNat 32 r - 1 ≠ 0 := fun h => h0 (by
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := r) (by omega)] at this
        simp only [show (1 : BitVec 32).toNat = 1 from rfl, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega)
      rw [show (BitVec.ofNat 32 r - 1 == 0) = false from by simpa using hne]
      simp [h0]
  have data₅ : t₅.mem.readW (Bs + BitVec.ofNat 64 dataSlot) 32 = P₀ + BitVec.ofNat 32 (8 * (n - (r - 1))) := by
    rw [mem₅, scr_sep (by simp only [dataSlot, leftSlot]; omega) (by decide) (by decide), Mem.readW_writeW_self32]
    have := hi.pos; have := hi.le
    rw [show 8 * (n - (r - 1)) = 8 * (n - r) + 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have left₅ : t₅.mem.readW (Bs + BitVec.ofNat 64 leftSlot) 32 = BitVec.ofNat 32 (r - 1) := by
    rw [mem₅, Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  by_cases hlast : r = 1
  · subst hlast
    left
    exact ⟨hev, esi₅, esp₅, rd₅, wr₅, frame₅, fun j hjn => done₅ j (by omega)⟩
  · right
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega,
      r - 1, by have := hi.pos; omega, ?_⟩
    refine ⟨by have := hi.pos; omega, by have := hi.le; omega, esi₅, esp₅, rd₅, wr₅, frame₅, data₅, left₅,
      done₅, ?_⟩
    intro j hj₁ hj₂
    have := hi.pos
    have := hi.le
    have hne : j ≠ n - r := by omega
    rw [other j hj₂ hne]
    exact hi.todo j (by omega) hj₂

end VG.Proof.Idea.X86

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

theorem loop_ok {z : Spec.Idea.Schedule} {P₀ : BitVec 32} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LCtx z P₀ n o) (hn : 1 ≤ n)
    (hdata : o.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 dataSlot) 32 = P₀)
    (hleft : o.mem.readW ((o.gpr .esi).setWidth 64 + BitVec.ofNat 64 leftSlot) 32 = BitVec.ofNat 32 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (P₀.setWidth 64 + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block ecbBody) .ne) o (LoopPost z P₀ n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z P₀ n m₀ o) (fun r t hi => step_ok hc r t hi) n o
    ⟨hn, Nat.le_refl _, rfl, rfl, rfl, rfl, Frame.refl _ _, ?_, hleft, fun j hj => by omega,
      fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, hdata]; exact (BitVec.add_zero _).symm

theorem ecb_wp (s : State) (hs : ecbContract.pre s) :
    WP isa ecb s (fun s' => abiPreserved s s' ∧ ecbContract.post s s') := by
  have hp := EPre.of hs
  have fB := hp.fB; have fSp := hp.fSp; have fD := hp.fD
  simp only [slots] at fB
  obtain ⟨o, ho, pi⟩ := prologue_run s hp
  let z := Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)
  let n := (arg s 2).toNat
  let B : Addr := (arg s 3).setWidth 64
  unfold ecb
  refine WP.seq (WP.of_runBlock ⟨o, ho, ?_⟩)
  have hc : LCtx z (arg s 1) n o := by
    refine ⟨⟨by rw [pi.esi, pi.wr, hp.wr]; simp, by rw [pi.esi]; simp only [slots]; omega,
      by rw [pi.esi, pi.sched]⟩, by rw [pi.wr, hp.wr]; simp [n], by rw [pi.esi]; exact hp.dDB, fD⟩
  have blocks₀ : ∀ j < n, Spec.Idea.blockAt o.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt s.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 (8 * j)) := fun j hj =>
    blockAt_congr (frame_bytes pi.frame (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact hp.dDB.sub_left (Offset.sub_base _ (by omega))) (by decide))
  refine WP.seq (WP.mono (Q := LoopPost z (arg s 1) n s.mem o) ?_ fun t ht => ?_)
  · have hz : isa.eval .e o = some (decide (n = 0)) := by
      show o.zf = _
      rw [pi.zf, show arg s 2 - 0 = arg s 2 from BitVec.sub_zero _]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    refine WP.ite _ hz (fun h0 => ?_) (fun h0 => ?_)
    · have h0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => by omega⟩
    · have h0 : n ≠ 0 := by simpa using h0
      refine loop_ok hc (Nat.pos_of_ne_zero h0) (by rw [pi.esi]; exact pi.data)
        (by rw [pi.esi, pi.left]; simp [n]) blocks₀
  · -- Restoring the registers.
    have esiT : t.gpr .esi = arg s 3 := ht.esi.trans pi.esi
    have savedT : ∀ j < 4, t.mem.readW (B + BitVec.ofNat 64 (savedSlot + 4 * j)) 32 = s.gpr (sreg j) := by
      intro j hj
      rw [← pi.saved j hj]
      refine ht.frame.readW (r := ⟨B + BitVec.ofNat 64 (savedSlot + 4 * j), 4⟩) (Region.contains_self _ _)
        (fun q hq => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (hp.dDB.sub_right (r₂' := ⟨B + BitVec.ofNat 64 (savedSlot + 4 * j), 4⟩)
          (Offset.sub_base _ (by simp only [savedSlot, slots]; omega))).symm
      · simp only [slotsR, pi.esi]
        exact Offset.disjoint _ (by simp only [savedSlot, t0Slot]; omega)
          (by simp only [savedSlot]; omega) (by simp only [t0Slot]; omega)
    have rdT : ∀ u : State, u.gpr .esi = arg s 3 → u.mem = t.mem → u.rd = t.rd → u.wr = t.wr →
        ∀ j, j < 4 → readSrc u (.mem (at_ .esi (savedSlot + 4 * j))) = some (s.gpr (sreg j)) :=
      fun u he hm hr hw j hj => by
        rw [load_src, he, addr_eq (by simp only [savedSlot]; omega), hm, savedT j hj]
        rw [he, addr_eq (by simp only [savedSlot]; omega), hr, hw, ht.rd, ht.wr, pi.rd, pi.wr, hp.wr]
        exact ⟨⟨(arg s 3).setWidth 64, 4 * slots⟩, by simp,
          Offset.contains_base _ (by simp only [savedSlot, slots]; omega) (by simp only [savedSlot]; omega)⟩
    obtain ⟨u₁, k₁, w₁, f₁⟩ := mov_run .ebx _ _ t (rdT t esiT rfl rfl rfl 0 (by decide))
    obtain ⟨u₂, k₂, w₂, f₂⟩ := mov_run .edi _ _ u₁ (rdT u₁ (by rw [f₁.reg .esi (by decide), esiT]) f₁.mem
      f₁.rd f₁.wr 2 (by decide))
    have e₂ : Keep [.ebx, .edi] t u₂ := (f₁.weaken (by decide)).trans (f₂.weaken (by decide))
    obtain ⟨u₃, k₃, w₃, f₃⟩ := mov_run .ebp _ _ u₂ (rdT u₂ (by rw [e₂.reg .esi (by decide), esiT]) e₂.mem
      e₂.rd e₂.wr 3 (by decide))
    have e₃ : Keep [.ebx, .edi, .ebp] t u₃ := (e₂.weaken (by decide)).trans (f₃.weaken (by decide))
    obtain ⟨u₄, k₄, w₄, f₄⟩ := mov_run .esi _ _ u₃ (rdT u₃ (by rw [e₃.reg .esi (by decide), esiT]) e₃.mem
      e₃.rd e₃.wr 1 (by decide))
    have e₄ : Keep [.ebx, .edi, .ebp, .esi] t u₄ := (e₃.weaken (by decide)).trans (f₄.weaken (by decide))
    refine WP.of_runBlock ⟨u₄, ?_, ⟨fun r hr => ?_, ?_⟩, ?_⟩
    · exact run_append (a := [_]) k₁ (run_append (a := [_]) k₂ (run_append (a := [_]) k₃ k₄))
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [f₄.reg .ebx (by decide), f₃.reg .ebx (by decide), f₂.reg .ebx (by decide), w₁]; rfl
      · exact w₄
      · rw [f₄.reg .edi (by decide), f₃.reg .edi (by decide), w₂]; rfl
      · rw [f₄.reg .ebp (by decide), w₃]; rfl
      · rw [e₄.reg .esp (by decide), ht.esp, pi.esp]
    · rw [e₄.mem]
      have hr₀ : ∀ q ∈ [(⟨(arg s 3).setWidth 64, 4 * slots⟩ : Region)],
          Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ q := fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hp.rB
      have h₁ := pi.frame.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (w := 32) (Region.contains_self _ _) hr₀
        (by decide)
      have hr₁ : ∀ q ∈ [(⟨(arg s 1).setWidth 64, 8 * n⟩ : Region), slotsR o],
          Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ q := fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hp.rD
        · simp only [slotsR, pi.esi]
          exact hp.rB.sub_right (r₂' := ⟨(arg s 3).setWidth 64 + BitVec.ofNat 64 t0Slot, 12⟩)
            (Offset.sub_base _ (by decide))
      have h₂ := ht.frame.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (w := 32) (Region.contains_self _ _) hr₁
        (by decide)
      rw [h₂, h₁]
    · show Spec.Idea.blocksAt u₄.mem _ _ = _
      rw [e₄.mem]
      exact blocksAt_eq _ _ _ _ _ ht.done

end VG.Proof.Idea.X86
