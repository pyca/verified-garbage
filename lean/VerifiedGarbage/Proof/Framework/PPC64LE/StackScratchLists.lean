module

public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# A scratch buffer on the stack, for a signature with lists of slices (PPC64LE)

`Verified.stackScratchLists` is `Verified.stackScratchL`
(`Proof/Framework/PPC64LE/StackScratch.lean`) for a signature that may have
lists of slices (`Param.slices`), whose descriptors and listed slices
`Sig.contract` reads from the memory on entry (`Sig.lists`). The push of
`withStackScratch`'s frame writes only its back chain, in the stack below the
stack pointer, which every buffer and list lies outside of: so the memory the
code starts with lists the same slices (`narrow_listsL`, by
`Sig.lists_eq_of_agree`), and agrees with the memory on entry within the
buffers and the lists (`narrow_agreeLists`). As on ARMv7
(`Arm.Verified.stackScratchL`), the precondition, postcondition and leak must
read memory only within the function's buffers and its lists of slices
(`hpre`, `hpost`, `hleak`). `pre_regsLists` and `pub_regsLists` are
`pre_regs` and `pub_regsL` for such a signature: the lists are read-only
regions, and the descriptors are public.
-/

@[expose] public section

namespace VG.PPC64LE

open VG.Impl.StackScratch.PPC64LE

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
      (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
      s.rd = ((bufRegionsL sig s).filter (!·.2)).map (·.1) ∧
      s.wr = ((bufRegionsL sig s).filter (·.2)).map (·.1) ∧
      (bufRegionsL sig s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) ∧
      (∀ r ∈ stackBelow s.sp stack, ∀ a ∈ bufRegionsL sig s, r.Disjoint a.1) ∧
      (∀ a ∈ bufRegionsL sig s, a.1.base.toNat + a.1.len ≤ 2 ^ 64) ∧
      Curry.apply (sig.words abi.ptrBits) pre (regArgs sig s) s.mem := by
  have hk' : (sig.words 64).length ≤ argRegs.length := by
    have : (sig.words 64).length ≤ 8 := hk
    simpa [argRegs] using this
  have hwf : (match stack with | 0 => True | n => n ≤ s.sp.toNat) ↔
      (stack = 0 ∨ stack ≤ s.sp.toNat) := by
    cases stack <;> simp
  have hz : (sig.words 64).length - argRegs.length = 0 := Nat.sub_eq_zero_of_le hk'
  simp only [Sig.contract, abi, List.length_map, hk', hz, ite_true, List.map_nil, List.append_nil]
  exact and_congr hwf Iff.rfl

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

/-- The buffers and the lists of slices lie outside the doubleword the
frame's push writes. -/
theorem frame_disjLists (hk : (sig.words abi.ptrBits).length < 8) (hb : 32 < bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ bufRegionsL sig s, ∀ x, b.1.Contains x 1 →
      ¬ (⟨s.sp - BitVec.ofNat 64 bytes, 8⟩ : Region).Contains x 1 := by
  rw [pre_regsLists (by omega)] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega)]; simp
  intro b hb' x hx hc
  exact (hres _ hbelow b hb').sub_left (frame_sub (stack := stack) s hb) _ hc hx

/-- The push keeps the memory outside the doubleword it writes. -/
theorem push_agree {s : State} {x : Addr}
    (h : ¬ (⟨s.sp - BitVec.ofNat 64 bytes, 8⟩ : Region).Contains x 1) :
    s.mem x = (s.mem.write (s.sp - BitVec.ofNat 64 bytes) 8 s.sp) x := by
  have hf : Frame [⟨s.sp - BitVec.ofNat 64 bytes, 8⟩] s.mem
      (s.mem.write (s.sp - BitVec.ofNat 64 bytes) 8 s.sp) :=
    Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine (hf x fun r hr hc => ?_).symm
  simp only [List.mem_singleton] at hr; subst hr
  exact h hc

/-- The memory the code starts with agrees with the memory on entry within
the function's buffers and its lists of slices. -/
theorem narrow_agreeLists (hk : (sig.words abi.ptrBits).length < 8) (hb : 32 < bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    ∀ b ∈ bufRegionsL sig s, ∀ a, b.1.Contains a 1 → s.mem a = (narrow sig e n bytes s).mem a :=
  fun b hb' a ha => push_agree (frame_disjLists hk hb hs b hb' a ha)

/-- The memory the code starts with lists the same slices as the memory on
entry. -/
theorem narrow_listsL (hk : (sig.words abi.ptrBits).length < 8) (hb : 32 < bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    Sig.lists abi.ptrBits (narrow sig e n bytes s).mem sig.params (regArgs sig s) =
      Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s) :=
  (Sig.lists_eq_of_agree _ fun r hr x hx => narrow_agreeLists hk hb hs (r, false)
    (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) x hx).symm

/-- The precondition of the contract without the buffer gives the one with it
in `narrow`, if the precondition reads memory only within the buffers and the
lists of slices. -/
theorem narrow_preLists (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size + 32 ≤ bytes)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pre (narrow sig e n bytes s) := by
  obtain ⟨hb0, -, -, hb3⟩ := hb
  have hagree := narrow_agreeLists (e := e) (n := n) hk hb0 hs
  have hlists := narrow_listsL (e := e) (n := n) hk hb0 hs
  rw [pre_regsLists (by omega)] at hs
  obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega
  have hlen := regArgs_length sig s (by omega)
  have hbufs : Sig.bufs (sig.withScratch nm e n).params
      (regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes + 32]) =
      Sig.bufs sig.params (regArgs sig s) ++
        [(⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩, true)] :=
    Sig.bufs_append_array abi.ptrBits nm e n _ sig.params _ hlen
  have hlistsW : Sig.lists abi.ptrBits (narrow sig e n bytes s).mem (sig.withScratch nm e n).params
      (regArgs sig s ++ [s.sp - BitVec.ofNat 64 bytes + 32]) =
      Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s) :=
    (Sig.lists_append_array abi.ptrBits _ nm e n _ sig.params _ hlen).trans hlists
  have hall : bufRegionsL (sig.withScratch nm e n) (narrow sig e n bytes s) =
      (Sig.bufs sig.params (regArgs sig s) ++
        [(⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩, true)]) ++
      (Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s)).map (fun r => (r, false)) := by
    rw [bufRegionsL, narrow_regArgs hk, hbufs, hlistsW]
  have hbelow : below s.sp (stack + bytes) ∈ stackBelow s.sp (stack + bytes) := by
    rw [stackBelow_pos _ (by omega)]; simp
  have hscrSub := buf_sub (stack := stack) (e := e) (n := n) s hb3
  have hscrD : ∀ a ∈ bufRegionsL sig s,
      a.1.Disjoint ⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩ :=
    fun a ha => (Region.Disjoint.symm (hres _ hbelow a ha)).sub_right hscrSub
  have hB : ∀ a ∈ Sig.bufs sig.params (regArgs sig s), a ∈ bufRegionsL sig s :=
    fun a ha => List.mem_append_left _ ha
  have hL : ∀ a ∈ (Sig.lists abi.ptrBits s.mem sig.params (regArgs sig s)).map (fun r => (r, false)),
      a ∈ bufRegionsL sig s := fun a ha => List.mem_append_right _ ha
  have hbase : (s.sp - BitVec.ofNat 64 bytes + 32).toNat = s.sp.toNat - bytes + 32 := by
    rw [sub_add_header _ (by omega), toNat_sub_ofNat' (by omega)]; omega
  refine (pre_regsLists (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mpr ?_
  rw [hall, narrow_regArgs hk, narrow_sp]
  refine ⟨.inr ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toNat_sub_ofNat' (by omega)]; omega
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
    · exact ((Offset.base_disjoint_below (s.sp - BitVec.ofNat 64 bytes) (n := stack) (k := bytes)
        (by have := s.sp.isLt; omega)).sub_left (Offset.sub_base (d := 32) _ (by omega))).symm
    · exact (hres _ hbelow a (hL a ha)).sub_left (below_below _ bytes stack)
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | rfl) | ha
    · exact hnw a (hB a ha)
    · show (s.sp - BitVec.ofNat 64 bytes + 32).toNat + n * e.size ≤ 2 ^ 64
      have := s.sp.isLt
      rw [hbase]; omega
    · exact hnw a (hL a ha)
  · refine Eq.mpr (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params pre _ _ hlen) _) ?_
    exact hpre _ _ _ hlen (fun b hb' a ha => hagree b (hB b hb') a ha)
      (fun r hr a ha => hagree (r, false) (hL _ (List.mem_map.mpr ⟨r, hr, rfl⟩)) a ha) hpr

/-- The public data of the contract without the buffer, with its leak, is
public in `narrow` for the contract with it, if the leak reads memory only
within the function's buffers and its lists of slices (`hleak`). -/
theorem narrow_pubLists (hk : (sig.words abi.ptrBits).length < 8) (hb : 32 < bytes)
    {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + bytes) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + bytes) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak) :
    (Sig.scratchContract abi sig nm e n pre post wa stack leak).pub (narrow sig e n bytes s₁)
      (narrow sig e n bytes s₂) := by
  have g₁ := narrow_agreeLists (e := e) (n := n) hk hb h₁
  have g₂ := narrow_agreeLists (e := e) (n := n) hk hb h₂
  rw [pub_regsLists (by omega)] at hp
  obtain ⟨⟨hsp, hlk⟩, hpa, hdesc⟩ := hp
  have l₁ := regArgs_length sig s₁ (by omega)
  have l₂ := regArgs_length sig s₂ (by omega)
  have hL : ∀ {s : State}, (sig.contract abi pre post wa (stack + bytes) leak).pre s →
      ∀ r ∈ Sig.lists abi.ptrBits (narrow sig e n bytes s).mem sig.params (regArgs sig s),
      ∀ x, r.Contains x 1 → (narrow sig e n bytes s).mem x = s.mem x := fun hs r hr x hx =>
    (narrow_agreeLists hk hb hs (r, false) (List.mem_append_right _
      (List.mem_map.mpr ⟨r, (narrow_listsL hk hb hs) ▸ hr, rfl⟩)) x hx).symm
  refine (pub_regsLists (sig := sig.withScratch nm e n)
    (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
    (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
    (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mpr ?_
  rw [narrow_regArgs hk, narrow_regArgs hk, narrow_sp, narrow_sp, hsp,
    show (sig.withScratch nm e n).params = sig.params ++ [((nm, .array true e n) : String × Param)]
      from rfl, Sig.descs_append_array abi.ptrBits nm e n _ sig.params _ l₁]
  refine ⟨⟨rfl, leakAgree_withScratchL hleak _ _ l₁ l₂
    (fun b hb' a ha => (g₁ b (List.mem_append_left _ hb') a ha).symm) (hL h₁)
    (fun b hb' a ha => (g₂ b (List.mem_append_left _ hb') a ha).symm) (hL h₂) hlk⟩,
    fun i hi => ?_, fun r hr i hi => ?_⟩
  rotate_left
  · have hx : r.Contains (r.base + BitVec.ofNat 64 i) 1 := Region.contains_ofNat r.base hi
    have hr' : r ∈ Sig.lists abi.ptrBits s₁.mem sig.params (regArgs sig s₁) :=
      Sig.descs_sub_lists _ _ _ _ r hr
    have hd := frame_disjLists hk hb h₁ (r, false)
      (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr', rfl⟩)) _ hx
    rw [← g₁ (r, false) (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr', rfl⟩)) _ hx,
      hdesc r hr i hi, narrow_mem]
    rw [hsp] at hd
    exact push_agree hd
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
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), l₁, l₂]

/-- `withStackScratch_run`, for a signature that may have lists of slices. -/
theorem withStackScratch_runLists {c : Prog isa} (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size + 32 ≤ bytes) {s : State}
    (hs : (sig.contract abi pre post wa (stack + bytes) leak).pre s) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrow sig e n bytes s) t s₃) (ha : abiPreserved (narrow sig e n bytes s) s₃) :
    Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) c) s
        (.addr (s.sp - BitVec.ofNat 64 bytes) :: t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hr2, -⟩ := argRegs_scratch _ hk
  rw [pre_regsLists (by omega)] at hs
  obtain ⟨hwf, -, -, -, -, -, -⟩ := hs
  have hsb : stack + bytes ≤ s.sp.toNat := by rcases hwf with h | h <;> omega
  have hpush : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, allocated]
    exact ite_eq_left ⟨hb0, hb1, hb2, by omega⟩
  have hblk : Exec isa (.block [.addSp (argRegs.getD (sig.words abi.ptrBits).length .r3) 32])
      (allocated bytes s) [] (scratchState sig bytes s) :=
    .block (by simp only [execBlock, isa, exec, show (32 : Nat) < 2 ^ 15 by decide, ite_true,
      Option.map_some, addrs, List.map_nil, List.append_nil, scratchState]; rfl)
  have hcov : Covers (s.wr ++ [⟨s.sp - BitVec.ofNat 64 bytes + 32, n * e.size⟩])
      (frameR bytes s :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., Region.contains_self' (by omega)⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := frameR bytes s :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrow sig e n bytes s).withRegions s.rd (frameR bytes s :: s.wr) =
      scratchState sig bytes s from rfl] at hw
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 64 bytes := ha.2.1.trans (narrow_sp s)
  have hpop : isa.pop (.free bytes) (allocated bytes s)
      (s₃.withRegions s.rd (frameR bytes s :: s.wr)) = some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions, allocated, hsp₃, List.head?_cons, List.tail_cons, hb0,
      hb1, hb2, and_self, ite_true, BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
    List.cons_append] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl, ?_⟩, rfl, rfl⟩
  · have hqr : q ≠ argRegs.getD (sig.words abi.ptrBits).length .r3 := fun h => hr2 (h ▸ hq)
    show s₃.gpr q = s.gpr q
    rw [ha.1 q hq, narrow_gpr]
    simp only [hqr, ↓reduceIte]
  · show s₃.lr = s.lr
    rw [ha.2.2, narrow_lr]

/-- Code verified for a function whose last argument, in a register, is a
scratch buffer of `n` elements `e`, with `stack` bytes of stack, is verified
for the function without it, which allocates the buffer in a frame of
`bytes` more bytes of stack (`withStackScratch`), with any leak, if its
precondition, postcondition and leak read memory only within the function's
buffers and its lists of slices (`hpre`, `hpost`, `hleak`, which holds of no
leak). The signature may have lists of slices. -/
theorem Verified.stackScratchLists {c : Prog isa}
    (h : Verified target c (Sig.scratchContract abi sig nm e n pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length < 8)
    (hb : 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ n * e.size + 32 ≤ bytes)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + bytes)).pre s)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak := by trivial) :
    Verified target (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) c)
      (sig.contract abi pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := regArgs_length sig
  have hrun : ∀ s, (sig.contract abi pre post wa (stack + bytes) leak).pre s → ∃ t s₃,
      Exec isa c (narrow sig e n bytes s) t s₃ ∧
      (Sig.scratchContract abi sig nm e n pre post wa stack leak).post (narrow sig e n bytes s) s₃ ∧
      Exec isa (withStackScratch bytes (argRegs.getD (sig.words abi.ptrBits).length .r3) c) s
        (.addr (s.sp - BitVec.ofNat 64 bytes) :: t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrow_preLists hk hb hpre hs)
    exact ⟨t, s₃, he, hq, withStackScratch_runLists hk hb hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_regs (by omega)]
    have hq' := (post_regs (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)
      (by rw [Sig.words_withScratch, List.length_append, List.length_singleton]; omega)).mp hq
    rw [narrow_regArgs hk] at hq'
    rw [hm, hg]
    have hq'' := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s (by omega))) _) s₃.mem) _) hq'
    have hag := narrow_agreeLists (e := e) (n := n) hk hb.1 hs
    exact hpost _ _ _ _ _ (hlen s (by omega))
      (fun b hb' a ha => (hag b (List.mem_append_left _ hb') a ha).symm)
      (fun r hr a ha => (hag (r, false) (List.mem_append_right _
        (List.mem_map.mpr ⟨r, (narrow_listsL hk hb.1 hs) ▸ hr, rfl⟩)) a ha).symm) hq''
  · obtain ⟨u₁, r₁, f₁, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨u₂, r₂, f₂, -, x₂, -⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pub_regsLists (by omega)).mp hp).1.1,
      hct _ _ _ _ _ _ (narrow_preLists hk hb hpre h₁) (narrow_preLists hk hb hpre h₂)
        (narrow_pubLists hk hb.1 h₁ h₂ hp hleak) f₁ f₂]

end

end VG.PPC64LE
