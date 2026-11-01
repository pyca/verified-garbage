module

public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A scratch buffer on the stack, for a signature with lists of slices (RISC-V)

`Verified.stackScratchLists` is `Verified.stackScratchL`
(`Proof/Framework/RISCV64/StackScratch.lean`) for a signature that may have
lists of slices (`Param.slices`), whose descriptors and listed slices
`Sig.contract` reads from the memory on entry (`Sig.lists`), as on PPC64LE
(`Proof/Framework/PPC64LE/StackScratchLists.lean`). On RISC-V the frame's
`alloc` writes no memory, so the code starts with the memory on entry: it
lists the same slices, and the precondition, postcondition and leak see the
memory they do without the frame, with no condition on what they read.
`pre_regsLists` and `pub_regsLists` are `pre_regs` and `pub_regsL` for such a
signature: the lists are read-only regions, and the descriptors are public.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.StackScratch.RISCV64

/-- The buffers of `sig` and its lists of slices, read only, and whether each
is writable. -/
def bufRegionsL (sig : Sig) (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (regArgs sig s) ++
    (Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s)).map fun r => (r, false)

/-- `pre_regs`, for a signature that may have lists of slices. -/
theorem pre_regsLists {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (sig.contract abi pre post wa stack leak).pre s ↔
      (s.sp.toNat % 16 = 0 ∧ (stack = 0 ∨ stack ≤ s.sp.toNat)) ∧
      s.rd = ((bufRegionsL sig s).filter (!·.2)).map (·.1) ∧
      s.wr = ((bufRegionsL sig s).filter (·.2)).map (·.1) ∧
      (bufRegionsL sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ bufRegionsL sig s, r.Disjoint a.1) ∧
      (∀ a ∈ bufRegionsL sig s, a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem ∧
      ∀ p ∈ Sig.alignedBufs sig.params (regArgs sig s), p.1.toNat % p.2 = 0 := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  have hz : (sig.words 64).length - argRegs.length = 0 := Nat.sub_eq_zero_of_le hk'
  simp only [Sig.contract, abi, List.length_map, hk', hz, ite_true, List.map_nil, List.append_nil,
    Bool.cond_true]
  refine and_congr ?_ Iff.rfl
  cases stack <;> simp

/-- `pub_regsL`, for a signature that may have lists of slices: their
descriptors are public too. -/
theorem pub_regsLists {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat} {s₁ s₂ : State}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hk : (sig.words abi.ptrBits).length ≤ 8) :
    (sig.contract abi pre post wa stack leak).pub s₁ s₂ ↔
      (s₁.sp = s₂.sp ∧ leakAgree leak (regArgs sig s₁) s₁.mem (regArgs sig s₂) s₂.mem) ∧
      (∀ i, (sig.params.flatMap (·.2.pubs)).getD i false = true →
        ((regArgs sig s₁).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64) =
          ((regArgs sig s₂).getD i 0).setWidth
            (((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64)) ∧
      ∀ r ∈ Sig.descs abi.ptrBits sig.params (regArgs sig s₁), ∀ i < r.len,
        s₁.mem (r.base + BitVec.ofNat 64 i) = s₂.mem (r.base + BitVec.ofNat 64 i) := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  simp only [Sig.contract, abi, List.length_map, hk', ite_true]
  cases leak with
  | none => simp only [leakAgree, and_true]; exact Iff.rfl
  | some f => exact Iff.rfl

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`, which has the same memory, and so lists the same slices. -/
theorem narrow_preLists (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre (narrow sig e n bytes s) := by
  obtain ⟨hb0, -, hb2, hb3⟩ := hb
  rw [pre_regsLists (by omega_arith)] at hs
  obtain ⟨⟨hal, hwf⟩, hrd, hwr, hpw, hres, hnw, hpr, hu⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega_arith
  have hlen := regArgs_length sig s (by omega_arith)
  have hbufs : Sig.bufs (sig.withScratch nm e n).params
      (regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes]) =
      Sig.bufs sig.params (regArgs sig s) ++
        [(⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  have hlistsW : Sig.lists abi.ptrBits s.mem (sig.withScratch nm e n).params
      (regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes]) =
      Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s) :=
    Sig.lists_append_array abi.ptrBits _ nm e n _ sig.params _ hlen
  have hall : bufRegionsL (sig.withScratch nm e n) (narrow sig e n bytes s) =
      (Sig.bufs sig.params (regArgs sig s) ++
        [(⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩, true)]) ++
      (Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s)).map (fun r => (r, false)) := by
    rw [bufRegionsL, narrow_regArgs hk, hbufs, narrow_mem, hlistsW]
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega_arith)]; simp
  have hscrSub := buf_sub (stack := stack) (e := e) (n := n) s hb3
  have hscrD : ∀ a ∈ bufRegionsL sig s,
      a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩ :=
    fun a ha => (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right hscrSub
  have hB : ∀ a ∈ Sig.bufs sig.params (regArgs sig s), a ∈ bufRegionsL sig s :=
    fun a ha => List.mem_append_left _ ha
  have hL : ∀ a ∈ (Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s)).map (fun r => (r, false)),
      a ∈ bufRegionsL sig s := fun a ha => List.mem_append_right _ ha
  have hbase : (s.sp - BitVec.ofNat 64 bytes).toNat = s.sp.toNat - bytes :=
    toNat_sub_ofNat' (by omega_arith)
  refine (pre_regsLists (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)).mpr ?_
  rw [hall, narrow_regArgs hk, narrow_sp]
  refine ⟨⟨by rw [hbase]; omega_arith, .inr (by rw [hbase]; omega_arith)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [narrow_rd, hrd, bufRegionsL, List.filter_append, List.map_append]; simp
  · simp only [narrow_wr, hwr, bufRegionsL, List.filter_append, List.map_append]
    simp [List.filter_map, Function.comp_def, filter_fun_false]
  · simp only [bufRegionsL, List.pairwise_append] at hpw
    obtain ⟨pB, pL, pBL⟩ := hpw
    simp only [List.pairwise_append, List.pairwise_singleton, List.mem_append, List.mem_singleton]
    refine ⟨⟨pB, trivial, fun a ha b hb _ => ?_⟩, pL, fun a ha b hb hab => ?_⟩
    · subst hb; exact hscrD a (hB a ha)
    · rcases ha with ha | rfl
      · exact pBL a ha b hb hab
      · exact (hscrD b (hL b hb)).symm
  · intro x hx a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hx
    rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | rfl) | ha
    · exact (hres _ hbelow a (hB a ha)).sub_left (below_below _ bytes stack)
    · exact (Offset.base_disjoint_below (s.sp - BitVec.ofNat 64 bytes) (n := stack) (k := n * e.size)
        (by have := s.sp.isLt; omega_arith)).symm
    · exact (hres _ hbelow a (hL a ha)).sub_left (below_below _ bytes stack)
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | rfl) | ha
    · exact hnw a (hB a ha)
    · show (s.sp - BitVec.ofNat 64 bytes).toNat + n * e.size ≤ 2 ^ 64
      have := s.sp.isLt
      rw [hbase]; omega_arith
    · exact hnw a (hL a ha)
  · exact Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) hpr
  · intro p hp
    rw [show (sig.withScratch nm e n).params = sig.params ++ [(nm, .array true e n)] from rfl,
      Sig.alignedBufs_append_array abi.ptrBits nm e n _ sig.params _ hlen] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hu p hp
    · split at hp
      · simp only [List.mem_singleton] at hp; subst hp
        refine Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Elem.align_dvd_eight e) (Nat.dvd_of_mod_eq_zero ?_))
        rw [hbase]; omega_arith
      · simp at hp

/-- The public data of the contract without the buffer, with its leak, is
public in `narrow` for the contract with it: `narrow` keeps the memory, so
the leak and the descriptors are the same. -/
theorem narrow_pubLists (hk : (sig.words abi.ptrBits).length < 8) {s₁ s₂ : State}
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  rw [pub_regsLists (by omega_arith)] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa, hdesc⟩ := hp
  have l₁ := regArgs_length sig s₁ (by omega_arith)
  have l₂ := regArgs_length sig s₂ (by omega_arith)
  refine (pub_regsLists (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_arith)).mpr ?_
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_sp, narrow_sp, hsp, narrow_mem, narrow_mem,
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.descs_append_array abi.ptrBits nm e n _ sig.params _ l₁]
  refine ⟨⟨rfl, ?_⟩, fun i hi => ?_, hdesc⟩
  · cases leak with
    | none => trivial
    | some f =>
      show Curry.apply _ (Curry.withScratch abi.ptrBits nm e n sig.params f) _ _ =
        Curry.apply _ (Curry.withScratch abi.ptrBits nm e n sig.params f) _ _
      rw [Curry.apply_withScratch abi.ptrBits nm e n sig.params f _ _ l₁,
        Curry.apply_withScratch abi.ptrBits nm e n sig.params f _ _ l₂]
      exact hlk
  have lp := Sig.pubs_length sig.params abi.ptrBits
  have hps : ((sig.params ++ [((nm, .array true e n) : String × Param)]).flatMap (·.2.pubs)) =
      sig.params.flatMap (·.2.pubs) ++ [true] := by
    simp [Param.pubs]
  rw [hps] at hi
  by_cases hik : i < (sig.words abi.ptrBits).length
  · have hW : (((sig.withScratch nm e n).words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 =
        ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD i 64 := by
      rw [Sig.words_withScratch, List.map_append]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [List.length_map]; exact hik)]
    rw [hW]
    simp only [List.getD_eq_getElem?_getD] at hi hpa ⊢
    rw [List.getElem?_append_left (by rw [l₁]; exact hik),
      List.getElem?_append_left (by rw [l₂]; exact hik)]
    rw [List.getElem?_append_left (by rw [lp]; exact hik)] at hi
    exact hpa i hi
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega_arith), List.getElem?_append_right (by omega_arith), l₁, l₂]

/-- `withStackScratch_run`, for a signature that may have lists of slices. -/
theorem withStackScratch_runLists {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₄ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₄) (ha : abiPreserved (narrow sig e n bytes s) s₄) :
    Exec isa (withStackScratch bytes (scratchReg sig) c) s t (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr = s₄.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr2, hra, -⟩ := argRegs_scratch _ hk
  rw [pre_regsLists (by omega_arith)] at hs
  obtain ⟨⟨-, hwf⟩, -, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega_arith
  have hpush : isa.push (.alloc bytes) s = some (allocd bytes s) := by
    show push (.alloc bytes) s = some (allocd bytes s)
    unfold push
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hb0, hb1, hb2, by omega_arith⟩) |>.trans rfl
  have hblk : Exec isa (.block [.addSp (scratchReg sig) 0]) (allocd bytes s) [] (scratchState sig bytes s) :=
    .block (by
      simp only [execBlock, isa, exec_addSp (show (0 : Nat) < 2048 by decide), Option.map_some, addrs,
        List.map_nil, List.append_nil, scratchState, BitVec.add_zero]
      rfl)
  have hcov : Covers (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩])
      (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) := by
    rintro a k ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  have hcov' : Covers (s.rd ++ (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes, n * e.size⟩]))
      (s.rd ++ (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) := by
    rintro a k ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := hcov a k ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) hcov' hcov
  rw [show (narrow sig e n bytes s).withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr) =
      scratchState sig bytes s from rfl] at hw
  have hsp₄ : s₄.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
  have hpop : isa.pop (.free bytes) (allocd bytes s)
      (s₄.withRegions s.rd (⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr)) =
        some (popState bytes s s₄) := by
    simp only [isa, pop, State.withRegions, allocd, hsp₄, List.head?_cons, List.tail_cons, hb0,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl, ?_⟩, rfl, rfl⟩
  · have hqr : q ≠ scratchReg sig := fun h => hr2 (by subst h; exact hq)
    show s₄.gpr q = s.gpr q
    rw [ha.1 q hq, narrow_gpr]
    simp only [hqr, ↓reduceIte]
  · show s₄.gpr .ra = s.gpr .ra
    rw [ha.2.2, narrow_gpr]
    simp only [show Reg.ra ≠ scratchReg sig from fun h => hra h.symm, ↓reduceIte]

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratch`), with any leak. The
signature may have lists of slices: the frame's `alloc` writes no memory, so
the precondition, postcondition, leak and lists see the memory they do
without it. -/
theorem Verified.stackScratchLists {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ n * e.size ≤ bytes)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    Verified target (withStackScratch bytes (scratchReg sig) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrow sig e n bytes s) s₃ ∧
      Exec isa (withStackScratch bytes (scratchReg sig) c) s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_preLists hk hb hs)
    exact ⟨t, s₃, he, hq, withStackScratch_runLists hk hb hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    show (sig.contract abi pre post wa (stack + bytes)).post s _
    rw [post_regs (by omega_using [hk])]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post) (wa := wa) (stack := stack)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega_using [hk])).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hg]
    exact Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega_using [hk]))) _) s₃.mem) _) hq'
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1]
    exact hct _ _ _ _ _ _ (narrow_preLists hk hb h₁) (narrow_preLists hk hb h₂) (narrow_pubLists hk hp) f₁ f₂

end

end VG.RISCV64
